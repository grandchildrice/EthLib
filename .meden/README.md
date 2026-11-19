# Continuing these EthLib contributions

The work items in `workspace.json` cover initialized TLS authentication, mixed-event gossip suppression, initialized mesh/fanout uniqueness and Ethereum deposit/BLS security.
The Gossip helper and RPC stages retain their own records.
Each retains its original requirement, named theorems, progress notes and next step.
The `evidence/` directory holds detailed check and mutation observations.
These are historical records; they do not restore approval or native proof authority.

Clone this fork's working branch on the other machine:

```sh
git clone --branch meden/assurance-workspace https://github.com/grandchildrice/EthLib.git
meden gui --workspace "$PWD/EthLib" --assets /path/to/meden/apps/web/dist
```

Build the latest Meden `main` and its browser assets (`npm ci && npm run build`) before opening the clone; select that build's `apps/web/dist` with `--assets`.
Open the printed session URL to see saved conversation and the whole-workspace navigation graph.
Choose the provider and model in the GUI before continuing with inference.
In **作業・履歴**, select a work item and inspect its requirement, theorem types, axioms and saved output.
**証明コードを読む** opens its source, with page controls for long files.
**この作業を再開** starts a new instruction from the task and bounded saved context after reviewing that device's processor connection.
Credentials and grants remain on each device.
Visible conversation is shared in the record; inspect it before publishing.

For **Leanを再チェック**, prepare the exact `lean-toolchain` distribution and the pinned dependency sources/artifacts on that device.
Checks run offline and do not install these prerequisites.
Missing tools or dependencies remain visible failures.
Reading the history and checking locally require no inference approval.
In the TUI, `/work` lists the tasks, `/work ID` shows one, `/work check ID` rechecks and `/work resume ID` continues after fresh processor review.
Press `/` at connection selection to open host commands.

After work, save the visible conversation, commit the changed source and `.meden` records, and push this branch.
Stop one Meden host before opening another writer for the same checkout.
Ordinary Git merges combine work from separate checkouts; Meden does not synchronize running sessions or install project dependencies.

The TLS result covers initialized accepted-call traces; transport, independent peer agreement and cryptographic handshake security remain outside it.
Gossip suppression needs a nondecreasing clock before the original TTL expiry and excludes IWANT replies.
Mesh/fanout uniqueness holds from the actual empty router across arbitrary finite mixtures of receive, join, leave, publish and heartbeat.
It requires lawful selectors at heartbeat, join and publish events, but no monotonicity of event times.
Both results use the actual router operations with one fixed parameter set and message-ID function.
Network delivery, packet/reassembly correspondence and scoring convergence remain outside these proofs.
BLS includes actual deposit registration, registry provenance, a single-registration reduction and adaptive shared-cache coupling.
Useful role-mask probability, zero/overlap losses and distribution averaging are still required for a complete Ethereum aggregate security bound.
