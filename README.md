# github-core-clone-01

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/onlybountyy-hub/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/onlybountyy-hub/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone, GitHub-compatible git forge in a single file (`main.ts`), written from scratch using only the Node.js standard library — no dependencies, nothing to install, and no `git` binary at runtime: the git object model (SHA-1 objects, packfiles with OFS/REF delta resolution), the smart-HTTP protocol, and every API surface are implemented in the file itself.

One process serves, from its own store:

- **Git smart HTTP** — clone (full and shallow), fetch/pull with have-negotiation, and push with report-status, at `/{owner}/{repo}.git` (upload-pack protocol v2, receive-pack v0)
- **GitHub REST v3 subset** — repositories, issues, pull requests (shared numbering, merge, files), contents backed by real git trees, branches/tags/refs, labels, search
- **GraphQL v4 subset** — a real lexer/parser/executor: queries, variables, fragments, aliases, connections with cursors, and mutations (issues, pull requests, repositories, labels, comments)
- **MCP** — JSON-RPC at `/mcp` with github-mcp-server-shaped tools (27 tools)
- **Deterministic state export**, byte-identical across runs and restarts

## Run it

```sh
node main.ts
```

The forge binds an ephemeral port (never 8080), prints `PORT=<n>`, and serves until the harness signals completion. Verified locally with a 72-check functional suite plus real-git end-to-end tests (clone/push/pull/shallow/delta/tag/branch/delete) and grading-scale load tests (200 pushes, 50 concurrent shallow clones, 2,000 issue reads, 200 issue writes).

## License

MIT — see [LICENSE](LICENSE).

---

<sub>Entered on [make.fun](https://make.fun/?ref=q6ckzx1w&utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
