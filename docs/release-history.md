# Release snapshots and downstream pins

Version v0.3.0 includes the mathematics at `44921f5914c5dbd40d2d532c2867adce0f519cb9`, including finite-order coordinate generation and regular-action faithfulness. Its release commit adds publication metadata and verification evidence. Lean remains v4.33.0 and official Mathlib v4.33.0 is `db584cd6d46c92f209a44c0f1c829460d327499d`.

| Historical consumer | Exact library pin | Library version |
| --- | --- | --- |
| Stafford38 v1.0.0/v1.0.1, verified `219668ef77b4ffddc1a503fd1ce61dbd48aa4b17` | `2fdc928835347a2638b6c85a4bfa770e3f70ed9e` | Source package v0.1.0, originally untagged; Lean/Mathlib v4.33.1 |
| Stafford38 v1.0.2, verified `79188b4b6c1ca7d21a50d6e965d0fb070f69b3d7` | `dfdd2da091a9d67e7a29cc7914f192d746a2400d` | Signed release v0.2.0; Lean/Mathlib v4.33.0 |
| Global Stafford, verified `d76051ce227f41c0fb21f114ffd61890f3b6b99b` | `faa64814d5a310dc925e330af58e000f129f1098` | Untagged post-v0.2.0 source with finite-order coordinate API |

The new downstream releases share the full v0.3.0 commit. These are verified source candidates; an actual Palomar submission pin requires its receipt. The Stafford38 v1.0.2 release description's stale pins were corrected on 2026-09-08; its tag was unchanged. Historical verification pins retain their meaning.

The author requested Zenodo coverage for every released version and the older dependency snapshots. Existing v0.2.0 was first released on 2026-09-05. Its publication event was re-emitted through GitHub's API on 2026-09-08 to request archival through the newly enabled integration; the signed tag and source contents were not changed. Historical snapshots must be labelled as archival deposits, without implying that an archival tag or deposit existed at the time of the old verification. DOI coverage is recorded only after Zenodo issues identifiers.

## Zenodo coverage

The existing v0.2.0 release is archived as DOI `10.5281/zenodo.22666206`,
under concept DOI `10.5281/zenodo.22666205`. The v0.1.0 source at `2fdc928`
received a signed archival tag and GitHub release on 2026-09-08 and is
archived as DOI `10.5281/zenodo.22666361`. That tag did not exist at the original verification.

The intermediate untagged Global Stafford dependency `faa64814` is preserved
byte-for-byte in [the historical source archive](releases/historical/algebraic-analysis-faa64814.tar.gz),
with its original commit and checksum in [provenance.json](releases/historical/provenance.json).
This source archive is included in the v0.3.0 tagged tree so Zenodo preserves
it along with the current release, without inventing a historical version tag.

Version v0.3.0 is archived at https://doi.org/10.5281/zenodo.22666517. Every file in the deposited ZIP was checked against the Git blob at release commit `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`; all 111 files match. The verification record is `docs/releases/historical/zenodo-22666517-verified.json`.
