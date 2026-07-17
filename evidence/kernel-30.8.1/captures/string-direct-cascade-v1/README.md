# `string-direct-cascade-v1` retained capture

This directory retains the accepted Set Z4 answer to the a12-kernel-lean-owned [`string-direct-cascade-v1` question](../../../scenarios/string-direct-cascade-v1/README.md). The packet was produced by a12-dmkits revision `c992afd62e4fa6148733a5538a3248c30fce60bf` from a clean worktree against kernel behavior 30.8.1. It establishes only the five named cases and the request-declared `kernel-route-confirmed-v1` projection.

The retained [`packet`](packet/PACKET.json) is the designated first capture. A second independently produced capture had the same complete receipt bytes and is intentionally omitted. The retained [`packet diff`](packet-diff/DIFF.json) records `identical: true` with no drift. The separate [`qualification report`](qualification/REPORT.json) records a satisfied policy with both kernel routes equal on all six required channels in all five cases. The two routes are distinct execution routes through one kernel implementation; the a12-dmkits interpreter remains triangulation rather than an oracle.

The out-of-band identities verified before and after ferrying are:

- packet [`RECEIPT.json`](packet/RECEIPT.json): `7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17`
- packet-diff [`RECEIPT.json`](packet-diff/RECEIPT.json): `b868d6fb57c38dd1b01edf56e58b507567c9c1a17265bcd692b822e97a4d0ce8`
- qualification [`RECEIPT.json`](qualification/RECEIPT.json): `f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64`
- scenario-mutation [`receipt`](process/scenario-mutation-receipt.json): `1ecff441da99528c798eef57a7152da0f7814de481dd4a9654b1f3eb472718c3`

The packet binds the exact request digest `4c5d4911ecacde819618b3b921b0bd30aa34b514cb0bbf3f0d2b735f21a0fd43`, model digest `3d21add02d259a8d1ad2e14475582513aec2f4e60176f1c02c81d40de88a895d`, and frozen V1 capabilities digest `b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca`. The successor process receipt uses `capture-scenario-mutation-receipt-v2` because its closed process-record shape adds an explicit rejected-predecessor binding and frozen-capabilities refusal; it does not mint a capture-capabilities, observation, packet, projection, or policy V2.

The immutable qualification [`PROFILE.json`](qualification/PROFILE.json) contains historical wording that the interpreter's public read surface cannot distinguish absent from present-empty. IF126 later added that distinction to the interpreter API, but frozen capture V1 deliberately does not consume it. Interpret the retained sentence as a V1 capture-lane and projection exclusion; do not rewrite the returned artifact.

Raw packet and sidecar bytes are immutable evidence. Project-owned typed projections, Lean replay code, findings, and status live outside this directory and may evolve only by naming these exact retained identities.
