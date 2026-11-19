"""Seen-cache lifetime across mixed router operations through the native bindings."""

from dataclasses import replace
from itertools import permutations
from typing import Literal

import pytest

from ethlib.networking import gossip
from ethlib.networking.gossip.router import (
    ClientChoices,
    Out,
    RouterState,
    heartbeat,
    join,
    leave,
    parameters,
    publish,
    receive_rpc,
)
from ethlib.networking.gossip.rpc import Control, IWant, Message, Rpc

# Source: libp2p/specs at c750236de43cd8b246a824b377dfdb26bae686db.
# The cache and replay rules are "Message Cache" and "Message Processing" of gossipsub-v1.0.md.
# The membership and heartbeat operations use "Topic Membership" and "Heartbeat" there.
# No official vectors cover mixed traces, so these cases state their expected outcomes by hand.

FORK = "fusaka"
TOPIC = "/eth2/b5303f2a/beacon_block/ssz_snappy"
PEER = b"peer"
MESSAGE = Message(data=b"block", topic=TOPIC)
MESSAGE_ID = gossip.message_id(FORK, TOPIC.encode(), MESSAGE.data)
PARAMS = replace(parameters(12_000, 32), seen_ttl=1)
CHOICES = ClientChoices(
    d_score=4,
    d_out=2,
    gossip_factor=(1, 4),
    gossip_round_up=True,
    flood_publish=False,
    prune_backoff_s=60,
    unsubscribe_backoff_s=10,
)
FIRST = 1_000
EXPIRY = FIRST + PARAMS.seen_ttl * 1_000
Operation = Literal["heartbeat", "join", "leave", "publish"]
ORDERS = tuple(permutations(("heartbeat", "join", "leave", "publish")))


def _receive(state: RouterState, now: int, rpc: Rpc | None = None) -> tuple[RouterState, Out]:
    return receive_rpc(
        fork=FORK,
        params=PARAMS,
        backoff_ms=30_000,
        prune_backoff_ms=60_000,
        standing={},
        validation={MESSAGE_ID: "accept"},
        now_ms=now,
        src=PEER,
        rpc=Rpc(publish=(MESSAGE,)) if rpc is None else rpc,
        state=state,
    )


def _step(operation: Operation, state: RouterState, now: int) -> tuple[RouterState, Out]:
    if operation == "heartbeat":
        return heartbeat(
            params=PARAMS,
            choices=CHOICES,
            ranking=(),
            standing={},
            now_ms=now,
            state=state,
        )
    if operation == "join":
        return join(params=PARAMS, standing={}, now_ms=now, topic=TOPIC, state=state)
    if operation == "leave":
        return leave(params=PARAMS, choices=CHOICES, now_ms=now, topic=TOPIC, state=state)
    return publish(
        fork=FORK,
        params=PARAMS,
        choices=CHOICES,
        standing={},
        now_ms=now,
        message=MESSAGE,
        state=state,
    )


@pytest.mark.parametrize("order", ORDERS)
@pytest.mark.parametrize("initial", ["receive", "publish"])
def test_mixed_trace_suppresses_replay_until_exact_expiry(
    order: tuple[Operation, ...], initial: str
) -> None:
    state = RouterState(topics=(TOPIC,))
    if initial == "receive":
        state, out = _receive(state, FIRST)
        assert out.delivered == (MESSAGE,)
    else:
        # No peer receives this publish, but its ID must still suppress a later received copy.
        state, out = _step("publish", state, FIRST)
        assert out == Out()
    assert state.seen == ((MESSAGE_ID, FIRST),)

    for offset, operation in enumerate(order, start=1):
        state, out = _step(operation, state, FIRST + offset)
        assert out.forward == ()
        assert out.delivered == ()
        assert state.seen == ((MESSAGE_ID, FIRST),)

    # Every ordering ends joined, so the last receive cannot pass merely by dropping the topic.
    state, _ = _step("join", state, EXPIRY - 2)
    state, out = _receive(state, EXPIRY - 1)
    assert out == Out()
    assert state.seen == ((MESSAGE_ID, FIRST),)

    # Expiry is strict: at exactly FIRST + TTL, a heartbeat removes the original entry.
    state, _ = _step("heartbeat", state, EXPIRY)
    assert (MESSAGE_ID, FIRST) not in state.seen
    state, out = _receive(state, EXPIRY)
    assert out.delivered == (MESSAGE,)
    assert state.seen == ((MESSAGE_ID, EXPIRY),)


def test_clock_rollback_after_expiry_does_not_meet_the_trace_hypothesis() -> None:
    state, _ = _receive(RouterState(topics=(TOPIC,)), FIRST)
    state, _ = _step("heartbeat", state, EXPIRY)
    assert state.seen == ()
    # A future heartbeat may expire the entry before a clock rollback returns within its TTL.
    # This outcome explains why the no-replay theorem requires nondecreasing event times.
    _, out = _receive(state, EXPIRY - 1)
    assert out.delivered == (MESSAGE,)


def test_iwant_answer_is_separate_from_repeated_forwarding_or_delivery() -> None:
    state, _ = _receive(RouterState(topics=(TOPIC,)), FIRST)
    state, _ = _step("heartbeat", state, FIRST + 1)
    _, out = _receive(
        state,
        FIRST + 2,
        Rpc(publish=(MESSAGE,), control=Control(iwant=(IWant(message_ids=(MESSAGE_ID,)),))),
    )
    assert out.forward == ()
    assert out.delivered == ()
    assert out.answers == ((PEER, MESSAGE),)
