# Reproducible Artifact Audit: Eleven Closest and Adjacent Formal Artifacts

## Scope and status

This audit records a source-level screen of eleven primary formal artifacts:

1. *Fair Operational Semantics* (FOS), PLDI 2023;
2. *Lilo*, OOPSLA 2025, Zenodo artifact version 3;
3. *Lawyer*, OOPSLA 2026;
4. *Spirea*, OOPSLA 2023;
5. Colvin and Dongol's PVS sources for *A General Technique for Proving
   Lock-Freedom*, SCP 2009;
6. *RoboCop*, OOPSLA 2024;
7. *Verifying General-Purpose RCU for Reclamation in Relaxed Memory
   Separation Logic*, PLDI 2025;
8. *CQS: A Formally-Verified Framework for Fair and Abortable
   Synchronization*, POPL 2023; and
9. *GenMC: A Model Checker for Weak Memory Models*, CAV 2021, source tag
   v0.6; and
10. *Burrow: A Proof Framework for Weak Memory*, CAV 2026; and
11. *Promising-ARM/RISC-V: A Simpler and Faster Operational Concurrency
    Model*, PLDI 2019.

The screen was repeated on 2026-07-31 against the exact local archives listed
below. It verifies archive integrity, extraction counts, named definitions and
theorems, and repository-wide keyword searches. It does **not** record a fresh
full Coq/Rocq/PVS/Agda compilation of A01–A05, A07, A08, A10, or A11. The A06
Treiber benchmark was rerun successfully with an isolated Python/Z3
environment; that is a tool execution, not a proof-assistant kernel check.
A08 and A11 were safely extracted and searched. A09 passed byte-level archive
integrity checks but was not generically extracted because it contains one
unsafe absolute symbolic link; its regular files were instead enumerated and
audited directly from the tar stream.

The source findings defeat broad priority claims for a formal fair weak-CAS
primitive, a machine-checked Treiber liveness result, a machine-checked
strong-CAS retry-loop termination result, and a mechanized hardware model that
allows independent store-exclusive failure. They do not, by themselves,
exhibit the exact integrated RC11/weak-CAS/Treiber positive-and-separation
result in the [claim card](claim-card.md).

## Archive identity and integrity

The canonical successful retrieval records are
[`manifest-20260730T224632Z.csv`](data/artifacts/manifest-20260730T224632Z.csv)
for A01–A03 and
[`manifest-20260730T233105Z.csv`](data/artifacts/manifest-20260730T233105Z.csv)
for A04, and
[`manifest-20260731T002021Z.csv`](data/artifacts/manifest-20260731T002021Z.csv)
for A05, and
[`manifest-20260731T033506Z.csv`](data/artifacts/manifest-20260731T033506Z.csv)
for A06–A07. A08's safe extraction and A09's deliberate extraction rejection
are recorded in
[`manifest-20260731T051403Z.csv`](data/artifacts/manifest-20260731T051403Z.csv).
The initial A11 retrieval and safe extraction are recorded in
[`manifest-20260731T090424Z.csv`](data/artifacts/manifest-20260731T090424Z.csv).
The current eleven-source no-extraction integrity revalidation is
[`manifest-20260731T091909Z.csv`](data/artifacts/manifest-20260731T091909Z.csv),
whose SHA-256 is
`8d8c700790081215f3784dc6db8a953218ddfeaa6b6a6221405d7811064d3613`
and which records zero failures.
The declared checksums also appear in
[`artifact-sources.csv`](artifact-sources.csv): A01–A10 declare MD5 values and
A11 declares a SHA-256 value, all of which match the corresponding actual
digest below. The two earlier artifact manifests record failed HTTP 406
attempts and are superseded by the successful retrievals above.

| ID | Primary artifact | Retrieved UTC | Local archive | Actual MD5 | Actual SHA-256 | Bytes | Extracted files |
|---|---|---:|---|---|---|---:|---:|
| A01 | [FOS, Zenodo 7711063](https://doi.org/10.5281/zenodo.7711063) | 2026-07-30 22:46:29 | [`fairness-source.zip`](data/artifacts/fairness-source.zip) | `f82b7e3f4d98a26bd74a8e3d98f7b607` | `d85a06e65827be3d322d0295a0fc5c987c3fdd931a3f6de6cbcf932fb0a5e094` | 460080 | 106 |
| A02 | [Lilo v3, Zenodo 14927742](https://doi.org/10.5281/zenodo.14927742) | 2026-07-30 22:46:31 | [`coq-lilo-v3.zip`](data/artifacts/coq-lilo-v3.zip) | `b80351a929c2552ae3bb388205438cae` | `9aefbbbe4ef9aabf2787f809bee10c97dd9b8299744aa12dd5df6cc899f901ef` | 676690 | 175 |
| A03 | [Lawyer, Zenodo 18457698](https://doi.org/10.5281/zenodo.18457698) | 2026-07-30 22:46:32 | [`lawyer-supplementary.zip`](data/artifacts/lawyer-supplementary.zip) | `587f4070067a1a32a60b2231a4d596fd` | `f93dfe82dabc529b6124c1cfa2e0d0db8058a73d24feb77e4b5343d9d3777ae2` | 1177683 | 114 |
| A04 | [Spirea, Zenodo 8314888](https://doi.org/10.5281/zenodo.8314888) | 2026-07-30 23:31:05 | [`spirea-oopsla23-artifact.zip`](data/artifacts/spirea-oopsla23-artifact.zip) | `739ecfe96352b3b48c95e3cad2aa8e5e` | `6acb678cde462c6d214e62b60a131fe2a3e394a58977d68855d99321875a066f` | 4215499 | 1474 |
| A05 | [Colvin–Dongol PVS bundle](https://brijeshdongol.github.io/mechanisation/SCP-2009-PVS.zip) | 2026-07-31 00:20:21 | [`colvin-dongol-2009-pvs.zip`](data/artifacts/colvin-dongol-2009-pvs.zip) | `d94e3786323df65a194f5279dbcd9cc3` | `ef949e62e988a57750a9765d44e41b68e988997309cbd4369292d803b3971710` | 51235 | 26 |
| A06 | [RoboCop, Zenodo 13626195](https://doi.org/10.5281/zenodo.13626195) | 2026-07-31 03:34:46 | [`robocop-oopsla24-artifact.tar.gz`](data/artifacts/robocop-oopsla24-artifact.tar.gz) | `e44465a21f5b47ca0fb0daa36a8cd873` | `b13daecf7f4a83a93175a4634be0b45ef1fd5e583d33f798938b1ae972d0de06` | 7516951 | 20427 |
| A07 | [General-Purpose RCU, Zenodo 15167032](https://doi.org/10.5281/zenodo.15167032) | 2026-07-31 03:35:05 | [`jung-2025-rcu-artifact.zip`](data/artifacts/jung-2025-rcu-artifact.zip) | `37f22d07e70d9af4cfe40711da39397e` | `e3c6379299ab1227479ed789822c450044ff15ac59b69b83761a680376297f08` | 785699 | 156 |
| A08 | [CQS, pinned public branch](https://github.com/Kotlin/kotlinx.coroutines/tree/970ef8c280dd8b934b3e89f78266e9b68b1a1290) | 2026-07-31 05:14:02 | [`cqs-proofs-970ef8c.tar.gz`](data/artifacts/cqs-proofs-970ef8c.tar.gz) | `6d8524aab1c4c92479dc3183f823a736` | `80fd24d87d1a35a6c6d49eb813659c815ceb8abe23254ab417fec05ad3e8de19` | 2178654 | 1203 |
| A09 | [GenMC v0.6, pinned source](https://github.com/MPI-SWS/genmc/tree/364e02afa1dec0e5c9fbedca6a2306d0ed5f1abf) | 2026-07-31 05:14:29 | [`genmc-v0.6-364e02a.tar.gz`](data/artifacts/genmc-v0.6-364e02a.tar.gz) | `ccd2414bb497f65f0060383b78327711` | `bf79f1c993418bdc131365b6e696b42778e9bc1824600e49c5c516c537c357b2` | 723433 | 4254 regular files; not generically extracted |
| A10 | [Burrow, pinned public source](https://github.com/sourcedennis/agda-burrow/tree/739a32764b6ebf74d0dec9d604e76919a85706f7) | 2026-07-31 05:42:30 | [`agda-burrow-739a327.tar.gz`](data/artifacts/agda-burrow-739a327.tar.gz) | `9d3f363779fdd2a2137a26a3fef6ac09` | `50761b1ffabd7c3fe0f94c277172dfe86ba23f57a3e2d903903bc76eba4a318a` | 32142 | 23 |
| A11 | [Promising-ARM/RISC-V supplement](https://sf.snu.ac.kr/publications/promising-arm-riscv-supp.zip) | 2026-07-31 09:04:24 | [`promising-arm-riscv-supp.zip`](data/artifacts/promising-arm-riscv-supp.zip) | `bd80b275090d5246b240b6c87ff12573` | `6ffeac6735494a9c7ee749b0a5731e8f2f1b5063a58876b972cd2a4b7ca105ca` | 800862 | 295 |

The following commands reproduce the local integrity checks from the
`weak-memory` repository root:

```bash
md5sum \
	  research/novelty-audit/data/artifacts/fairness-source.zip \
	  research/novelty-audit/data/artifacts/coq-lilo-v3.zip \
	  research/novelty-audit/data/artifacts/lawyer-supplementary.zip \
	  research/novelty-audit/data/artifacts/spirea-oopsla23-artifact.zip \
	  research/novelty-audit/data/artifacts/colvin-dongol-2009-pvs.zip \
	  research/novelty-audit/data/artifacts/robocop-oopsla24-artifact.tar.gz \
	  research/novelty-audit/data/artifacts/jung-2025-rcu-artifact.zip \
	  research/novelty-audit/data/artifacts/cqs-proofs-970ef8c.tar.gz \
	  research/novelty-audit/data/artifacts/genmc-v0.6-364e02a.tar.gz \
	  research/novelty-audit/data/artifacts/agda-burrow-739a327.tar.gz \
	  research/novelty-audit/data/artifacts/promising-arm-riscv-supp.zip

sha256sum \
	  research/novelty-audit/data/artifacts/fairness-source.zip \
	  research/novelty-audit/data/artifacts/coq-lilo-v3.zip \
	  research/novelty-audit/data/artifacts/lawyer-supplementary.zip \
	  research/novelty-audit/data/artifacts/spirea-oopsla23-artifact.zip \
	  research/novelty-audit/data/artifacts/colvin-dongol-2009-pvs.zip \
	  research/novelty-audit/data/artifacts/robocop-oopsla24-artifact.tar.gz \
	  research/novelty-audit/data/artifacts/jung-2025-rcu-artifact.zip \
	  research/novelty-audit/data/artifacts/cqs-proofs-970ef8c.tar.gz \
	  research/novelty-audit/data/artifacts/genmc-v0.6-364e02a.tar.gz \
	  research/novelty-audit/data/artifacts/agda-burrow-739a327.tar.gz \
	  research/novelty-audit/data/artifacts/promising-arm-riscv-supp.zip

unzip -tq research/novelty-audit/data/artifacts/fairness-source.zip
unzip -tq research/novelty-audit/data/artifacts/coq-lilo-v3.zip
unzip -tq research/novelty-audit/data/artifacts/lawyer-supplementary.zip
unzip -tq research/novelty-audit/data/artifacts/spirea-oopsla23-artifact.zip
unzip -tq research/novelty-audit/data/artifacts/colvin-dongol-2009-pvs.zip
tar -tzf research/novelty-audit/data/artifacts/robocop-oopsla24-artifact.tar.gz >/dev/null
unzip -tq research/novelty-audit/data/artifacts/jung-2025-rcu-artifact.zip
tar -tzf research/novelty-audit/data/artifacts/cqs-proofs-970ef8c.tar.gz >/dev/null
tar -tzf research/novelty-audit/data/artifacts/genmc-v0.6-364e02a.tar.gz >/dev/null
tar -tzf research/novelty-audit/data/artifacts/agda-burrow-739a327.tar.gz >/dev/null
unzip -tq research/novelty-audit/data/artifacts/promising-arm-riscv-supp.zip

find research/novelty-audit/data/artifacts/extracted/fairness-source \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/coq-lilo-v3 \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/lawyer-supplementary \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/spirea-oopsla23-artifact \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/colvin-dongol-2009-pvs \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/robocop-oopsla24-artifact.tar \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/jung-2025-rcu-artifact \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/cqs-proofs-970ef8c.tar \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/agda-burrow-739a327.tar \
  -type f | wc -l
find research/novelty-audit/data/artifacts/extracted/promising-arm-riscv-supp \
  -type f | wc -l

# Revalidate all eleven archives without extraction. This deliberately avoids
# following GenMC's unsafe absolute symlink.
python3 research/novelty-audit/scripts/fetch_artifacts.py --no-extract
```

All archive integrity tests passed. A01--A08 and A10--A11 passed the path-safe
extraction policy. A09's one absolute symbolic link,
`include/cassert -> /home/michalis/Documents/genmc-tool/include/assert.h`,
was rejected without writing it; 4,254 regular files, 1,093 directories, and
that single link were enumerated from the tar headers. The repeated hashes,
byte counts, and file counts matched the canonical manifests.
`fetch_artifacts.py` accepts ZIP and gzip-compressed tar archives, rejects
links and special tar members, and validates every extraction target before
writing it.

## A01: Fair Operational Semantics

### Artifact identity and build boundary

The artifact identifies itself as the Coq development for *Fair Operational
Semantics* and gives a Coq 8.15.0 build using `./configure` and
`make build -j`
([README, lines 1-22](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/README.md#L1-L22)).
Its own map identifies `WMM.v` as the fair weak-memory module and maps the
weak-memory ticket-lock and client results to `TicketLockW.v`,
`LockClientW.v`, and `LockClientWAll.v`
([README, lines 24-90](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/README.md#L24-L90)).

### Direct source findings

1. **A formal weak-CAS primitive is present.** The sequentially consistent
   memory module chooses `val` as its fairness identifier type
   ([`SCM.v`, lines 8-16](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/SCM.v#L8-L16)).
   It defines ordinary strong CAS at lines 133-148 and its wrapper at lines
   185-197. `cas_weak_fun` then adds a nondeterministic Boolean choice; its
   false branch checks permission, emits a `Fair` event that marks exactly the
   pointer argument as `Flag.fail`, and returns `false`
   ([`SCM.v`, lines 199-220](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/SCM.v#L199-L220)).
   Both `"cas"` and `"cas_weak"` are registered in the module
   ([`SCM.v`, lines 245-255](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/SCM.v#L245-L255)).

2. **The failure event has a well-founded progress interpretation.** The event
   language defines `fail`, `emp`, and `success`, and exposes a
   fairness-map-valued `Fair` event
   ([`Event.v`, lines 8-14 and 44-49](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/semantics/Event.v#L8-L49)).
   A `fair_update` requires a strict decrease of the well-founded index on
   `Flag.fail`, equality on `Flag.emp`, and imposes no constraint on
   `Flag.success`
   ([`FairBeh.v`, lines 126-140](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/semantics/FairBeh.v#L126-L140)).

   **Audit inference:** on a fair behavior, an infinite suffix consisting only
   of failures for the same pointer would require an infinite descending chain
   at that pointer. The well-founded update rule is therefore designed to
   exclude that all-spurious suffix. This is a semantic inference from the
   definitions, not a separately named weak-CAS theorem found in the artifact.

3. **The mechanized weak-memory case study does not use CAS.** `WMM.v` imports
   the Promising libraries, defines a visibility/missed-write fairness map, and
   emits it from load, store, and fetch-and-add
   ([`WMM.v`, lines 5-6 and 38-128](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/WMM.v#L5-L128)).
   The weak-memory module registers only `"store"`, `"load"`, and `"faa"`
   ([`WMM.v`, lines 131-137](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/WMM.v#L131-L137)).
   The ticket-lock implementation obtains a ticket with FAA, spins with load,
   and unlocks with load/store
   ([`TicketLockW.v`, lines 30-69](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/TicketLockW.v#L30-L69)).

4. **The checked result is ticket-lock/client refinement.**
   `ticketlock_fair` has type
   `ModSim.mod_sim AbsLockW.mod TicketLockW.mod`
   ([`TicketLockW.v`, lines 2571-2626](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/TicketLockW.v#L2571-L2626)).
   `LockClientWCorrect.correct` supplies the client simulation
   ([`LockClientW.v`, lines 1397-1455](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/LockClientW.v#L1397-L1455)),
   and `client_all` states the whole-program improvement from the nondeterministic
   specification schedule to the FIFO-scheduled ticket-lock client
   ([`LockClientWAll.v`, lines 42-58](data/artifacts/extracted/fairness-source/fairness-pldi23-artifact/src/example/LockClientWAll.v#L42-L58)).

5. **No use of `cas_weak` was found beyond definition and registration.** The
   repository-wide command below returns only `SCM.v:199` and `SCM.v:253`:

   ```bash
   rg -n --glob '*.v' 'cas_weak' \
     research/novelty-audit/data/artifacts/extracted/fairness-source/fairness-pldi23-artifact
   ```

### Claim boundary imposed by FOS

FOS rules out claiming the first formal weak-CAS fairness mechanism, the first
generic mechanized framework capable of expressing primitive fairness, or the
first formal mechanism that excludes a fixed-address all-spurious suffix. The
artifact screen did not find a Treiber client, a use of `cas_weak` in a proof,
an RC11 execution-graph all-spurious witness, an independence theorem, or an
unbounded system-wide response theorem. FOS therefore narrows, but does not
source-level subsume, the exact candidate conjunction.

Primary paper: [Lee et al., *Fair Operational Semantics*](https://sf.snu.ac.kr/publications/fairness.pdf),
[DOI 10.1145/3591253](https://doi.org/10.1145/3591253).

## A02: Lilo, artifact version 3

### Artifact identity and build boundary

The artifact identifies itself as the Coq development for *Lilo* and prescribes
an OCaml 4.14.2 opam switch, `./configure`, and `make -j`
([README, lines 1-18](data/artifacts/extracted/coq-lilo-v3/coq-lilo/README.md#L1-L18)).
Its case-study map identifies both the FOS weak-memory ticket-lock port and the
Treiber and elimination-stack specifications
([README, lines 144-163](data/artifacts/extracted/coq-lilo-v3/coq-lilo/README.md#L144-L163)).

### Direct source findings

1. **The Treiber implementation uses strong CAS.** `push_loop` and `pop_loop`
   call the operation named `"cas"` at `Code.v:19` and `Code.v:41`;
   neither calls `"cas_weak"`
   ([`treiber/Code.v`, lines 12-47](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/treiber/Code.v#L12-L47)).
   The memory record is one global heap-like contents map plus a next-block
   counter
   ([`SCMem.v`, lines 67-76](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/SCMem.v#L67-L76)).
   Its ordinary `cas` updates exactly when the current and expected values
   compare equal and reports failure on mismatch
   ([`SCMem.v`, lines 161-176](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/SCMem.v#L161-L176)).
   Module calls insert a `Yield` before entering the callee, exposing
   interleaving between memory calls
   ([`Linking.v`, lines 60-79](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/semantics/Linking.v#L60-L79)).

2. **A fair weak-CAS primitive is co-located but unused.** `cas_weak_fun`
   nondeterministically takes either the ordinary CAS path or a
   permission-checked spurious-failure path that emits an address-specific
   `Fair` failure
   ([`SCMem.v`, lines 222-257](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/SCMem.v#L222-L257)).
   Both operations are registered
   ([`SCMem.v`, lines 282-292](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/SCMem.v#L282-L292)).
   The inherited fairness update again requires strict well-founded descent on
   failure
   ([`FairBeh.v`, lines 125-140](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/semantics/FairBeh.v#L125-L140)).

3. **Machine-checked Treiber liveness specifications are present.** The
   liveness invariant carries progress credits at
   `SpecHOCAP.v:61-79`. `Treiber_push_spec` is stated at lines 203-219,
   and its proof explicitly splits an equal-head branch labelled “CAS success”
   from a different-head branch labelled “CAS fail” at lines 311-408
   ([`treiber/SpecHOCAP.v`, lines 203-219 and 311-408](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/treiber/SpecHOCAP.v#L203-L408)).
   `Treiber_pop_spec` is stated at lines 411-432
   ([`treiber/SpecHOCAP.v`, lines 411-432](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/treiber/SpecHOCAP.v#L411-L432)).

4. **The checked closed client is finite and specific.** It contains one push
   thread and one repeatedly popping thread
   ([`treiber/ClientCode.v`, lines 15-35](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/treiber/ClientCode.v#L15-L35)).
   `client_all` compares the specification under a nondeterministic scheduler
   with the client under a FIFO-set scheduler, while `client_fair_sched` gives
   the nondeterministic-scheduler improvement
   ([`treiber/ClientAdeqLat.v`, lines 195-229](data/artifacts/extracted/coq-lilo-v3/coq-lilo/src/example/treiber/ClientAdeqLat.v#L195-L229)).
   The associated paper's Section 7.2, pages 23-24, explains the finite-use
   obligation and relies on failed CAS indicating a successful interfering
   head update.

5. **No connection from `cas_weak` to Treiber was found.** The repository-wide
   command below returns only the definition at `SCMem.v:236` and registration
   at `SCMem.v:290`:

   ```bash
   rg -n --glob '*.v' 'cas_weak' \
     research/novelty-audit/data/artifacts/extracted/coq-lilo-v3/coq-lilo
   ```

### Claim boundary imposed by Lilo

Lilo rules out any claim to the first machine-checked Treiber liveness or
termination-guaranteeing logical-atomic specification. It is the closest
artifact-level integration threat because the same source tree contains both
that strong-CAS Treiber result and an unused fair weak-CAS primitive. The
screen found no theorem connecting them. The Treiber result uses a
single-global-heap interleaving semantics, strong CAS, and a finite-use
obligation; it supplies neither the target RC11 finite-prefix carrier nor an
integrated all-spurious separation nor the target unbounded system-wide
response conclusion.

Primary paper: [Lee et al., *Lilo*](https://iris-project.org/pdfs/2025-oopsla-lilo.pdf),
[DOI 10.1145/3720525](https://doi.org/10.1145/3720525).

## A03: Lawyer

### Artifact identity and build boundary

The supplementary README identifies a Rocq development divided into Trillium
and Lawyer sources, gives an OCaml 5.2.0/opam setup and `make -j 5`, and points
to `check/check.v` for the final results and their printed assumptions
([README, lines 1-45](data/artifacts/extracted/lawyer-supplementary/README.md#L1-L45)).
It maps the delaying counter example to termination under any scheduler and
the other relevant examples to fair-scheduler termination
([README, lines 61-83](data/artifacts/extracted/lawyer-supplementary/README.md#L61-L83)).

### Direct source findings

1. **The execution model has strong CAS, not weak CAS.** The HeapLang state
   contains one heap map
   ([`heap_lang/lang.v`, lines 187-191](data/artifacts/extracted/lawyer-supplementary/lawyer/heap_lang/lang.v#L187-L191)).
   In its `head_step` semantics, `CmpXchgS` sets the success bit to
   `bool_decide (vl = v1)` and updates exactly when that bit is true
   ([`heap_lang/lang.v`, lines 587-648](data/artifacts/extracted/lawyer-supplementary/lawyer/heap_lang/lang.v#L587-L648)).
   There is no compare-equal spurious-failure branch.

2. **The fairness layer formalizes weak scheduler fairness.**
   `fair_by'` is defined at lines 177-180; `weakly_fair` at lines 229-234;
   `fair_by'_weakly_fair` proves their equivalence at lines 238-262; and
   execution fairness is `fair_ex` at lines 272-279
   ([`fairness/fairness.v`, lines 177-180 and 229-279](data/artifacts/extracted/lawyer-supplementary/lawyer/fairness/fairness.v#L177-L279)).

3. **A machine-checked strong-CAS retry-loop result is present.**
   `incr_impl` repeatedly loads and CAS-increments a counter
   ([`lf_counter.v`, lines 111-116](data/artifacts/extracted/lawyer-supplementary/lawyer/lawyer/examples/lf_counter/lf_counter.v#L111-L116)).
   `counter_client` forks one increment and performs another
   ([`lf_counter.v`, lines 395-404](data/artifacts/extracted/lawyer-supplementary/lawyer/lawyer/examples/lf_counter/lf_counter.v#L395-L404)).
   `lf_counter_termination` proves that every valid trace from that client is
   terminating
   ([`lf_counter_adequacy.v`, lines 49-64](data/artifacts/extracted/lawyer-supplementary/lawyer/lawyer/examples/lf_counter/lf_counter_adequacy.v#L49-L64)).

4. **The artifact's final result list contains no stack theorem.**
   `check/check.v` imports the ticket-lock, nondeterminism, bounded-termination,
   counter, and runtime-bound cases, collects their adequacy results, and
   invokes `Print Assumptions`
   ([`check/check.v`, lines 1-26](data/artifacts/extracted/lawyer-supplementary/lawyer/check/check.v#L1-L26)).
   The top-level README maps the ticket-lock case and its closed-program
   termination result at lines 119-138
   ([README, lines 119-138](data/artifacts/extracted/lawyer-supplementary/README.md#L119-L138)).

5. **No Treiber, weak-CAS, or spurious-failure source was found.** This
   repository-wide adversarial scan produced no hits:

   ```bash
   rg -n --glob '*.v' -i \
     'Treiber|elimination[ _-]*stack|cas_weak|weak[ _-]*cas|spurious' \
     research/novelty-audit/data/artifacts/extracted/lawyer-supplementary/lawyer
   ```

   The example directories are `const_term`, `eo_fin`, `lf_counter`, `nondet`,
   `rt_bound`, and `ticketlock`.

### Claim boundary imposed by Lawyer

Lawyer rules out broad priority language for machine-checked modular
termination reasoning over strong-CAS retry loops and fair closed concurrent
programs. The artifact screen found no Treiber theorem, weak-CAS semantics,
RC11 execution graph, primitive-justice dimension, all-spurious separation,
or system-wide lock-freedom theorem. Its closest overlap is the
machine-checked termination proof for a two-increment strong-CAS counter.

Primary paper: [Namakonov et al., *Lawyer*](https://iris-project.org/pdfs/2026-oopsla-lawyer.pdf),
[DOI 10.1145/3798240](https://doi.org/10.1145/3798240). The latter is the
verified Lawyer DOI; `10.1145/3729250` identifies a different paper.

## A04: Spirea

### Artifact identity and build boundary

The artifact identifies itself as the Coq development for *Spirea*, documents
Coq 8.17.1, and states that the default `make -jN` target builds the project
([README, lines 1–43](data/artifacts/extracted/spirea-oopsla23-artifact/README.md#L1-L43)).
Its source overview maps the language semantics, low- and high-level logics,
adequacy results, and case studies
([README, lines 45–87](data/artifacts/extracted/spirea-oopsla23-artifact/README.md#L45-L87)).
This audit verified archive integrity and inspected the source but did not
perform the documented approximately 15-minute Coq rebuild.

### Direct source findings

1. **The language uses exact-match CAS, not genuinely weak CAS.** The
   successful compare-exchange head step has no mismatch premise, while the
   failure head step explicitly requires the value read from memory to differ
   from the expected value
   ([`lang.v`, lines 248–260](data/artifacts/extracted/spirea-oopsla23-artifact/src/lang/lang.v#L248-L260)).
   The primitive proof chooses success on equality and failure only on
   inequality
   ([`primitive_laws.v`, lines 881–926](data/artifacts/extracted/spirea-oopsla23-artifact/src/base/primitive_laws.v#L881-L926)).
   Thus the semantics has no compare-equal spurious-failure branch.

2. **A durable Treiber implementation and proof are present.** The case-study
   file defines `mk_stack`, retrying `push`, retrying `pop`, and `sync`
   ([`durable_treiber_stack.v`, lines 28–70](data/artifacts/extracted/spirea-oopsla23-artifact/src/examples/durable_treiber_stack.v#L28-L70)).
   It proves post-crash representation lemmas and Hoare-style specifications
   for construction, push, pop, and sync
   ([`durable_treiber_stack.v`, lines 239–480](data/artifacts/extracted/spirea-oopsla23-artifact/src/examples/durable_treiber_stack.v#L239-L480)).

3. **The checked case study is safety, not liveness or verified
   linearizability.** Section 6.3 presents thread- and crash-safety with null
   recovery. Section 6.3.2 explicitly says the supplied specification does not
   imply linearizability or the LIFO property. No fairness, liveness,
   lock-freedom, wait-freedom, spurious-failure, or progress theorem was found
   in the project source by the recorded repository-wide scan.

4. **The memory model is adjacent but does not subsume RC11.** Spirea uses a
   view-based operational release/acquire weak-persistent-memory semantics that
   recasts explicit epoch persistency. Section 1.2 explicitly leaves a formal
   correspondence with the original declarative formulation to future work.
   The source does not provide the target coherent RC11 finite-prefix carrier
   or prefix-finite `mo`/`fr` progress assumptions.

5. **Mechanization caveat.** The durable Treiber file itself contains no
   `Admitted`, `admit`, or `Axiom`. A repository-wide scan finds admitted
   obligations in the separate unfinished
   [`epoch_persistency.v`](data/artifacts/extracted/spirea-oopsla23-artifact/src/examples/epoch_persistency.v)
   example. That file is not imported by the durable Treiber case study. This
   source separation is useful evidence, but only a clean rebuild plus
   `Print Assumptions` or `coqchk` would establish the exact trusted boundary.

### Claim boundary imposed by Spirea

Spirea rules out broad wording such as the first machine-checked Treiber
safety proof under any weak-memory or persistent-memory semantics. It does not
subsume the candidate conjunction: its CAS is exact-match, its verified
specification is explicitly weaker than linearizability/LIFO, it proves no
progress result, and it has no scheduler/memory/primitive-fairness separation
or all-spurious execution.

Primary paper: [Vindum and Birkedal, *Spirea*](https://cs.au.dk/~birke/papers/spirea-2023.pdf),
[DOI 10.1145/3622820](https://doi.org/10.1145/3622820).

## A05: Colvin–Dongol PVS sources

### Artifact identity and build boundary

The author-hosted archive is linked as the PVS source bundle for Colvin and
Dongol's 2009 *A General Technique for Proving Lock-Freedom*. It contains 26
files: PVS theories and proof files for the Michael–Scott queue and a bounded
array queue, auxiliary variants, strategies, and a standalone legacy
`treiber.pvs`. No README, pinned PVS version, or scripted clean-build command
is included. This audit therefore verifies archive/source identity and proof
file presence, not replay under an inferred PVS toolchain.

### Direct source findings

1. **The completed proof families are queue cases.** The archive contains
   `msq.prf`, `msqEnq.prf`, `msqDeq.prf`, `msqCounters.prf`, `modmsq.prf`,
   `modmsqCounters.prf`, `cgq.prf`, and `cgqMod.prf`. These correspond to the
   Michael–Scott and bounded-array queue cases advertised for the 2009 generic
   method.

2. **A substantial Treiber theory is present, but its proof archive is
   incomplete.** `treiber.pvs` models push and pop, defines equality/mismatch
   branches for the update steps, and proposes a global well-founded measure
   ([`treiber.pvs`, lines 1–211](data/artifacts/extracted/colvin-dongol-2009-pvs/pvs/treiber.pvs#L1-L211);
   [`treiber.pvs`, lines 218–386](data/artifacts/extracted/colvin-dongol-2009-pvs/pvs/treiber.pvs#L218-L386)).
   The archive contains no `treiber.prf`. More decisively, the same source
   marks `trans_closure_wf_wf` and `finiteness_conjecture` with the comments
   “Will not prove”
   ([`treiber.pvs`, lines 393–414](data/artifacts/extracted/colvin-dongol-2009-pvs/pvs/treiber.pvs#L393-L414)).
   It must not be presented as a completed 2009 machine-checked Treiber case.

   The following presence/absence checks reproduce this disposition:

   ```bash
   find research/novelty-audit/data/artifacts/extracted/colvin-dongol-2009-pvs/pvs \
     -maxdepth 1 -type f -name '*.prf' -printf '%f\n' | sort
   test ! -e \
     research/novelty-audit/data/artifacts/extracted/colvin-dongol-2009-pvs/pvs/treiber.prf
   rg -n 'Will not prove' \
     research/novelty-audit/data/artifacts/extracted/colvin-dongol-2009-pvs/pvs/treiber.pvs
   ```

3. **The modeled CAS behavior is strong.** The successful push and pop
   branches require equality of the recorded and current head (including the
   modification counter), while the failure branches require the negation of
   that match
   ([`treiber.pvs`, lines 167–177](data/artifacts/extracted/colvin-dongol-2009-pvs/pvs/treiber.pvs#L167-L177)).
   There is no equal-value spurious-failure branch.

4. **The source has no target weak-memory or fairness dimensions.** It is an
   atomic global-state interleaving theory. A source-wide scan found no RC11,
   weak-CAS, spurious-failure, scheduler-fairness, memory-fairness, or
   primitive-justice definition. Its progress structure is the classical
   global well-founded-order method.

5. **The 2007 result remains separate prior art.** Colvin and Dongol's 2007
   ICTAC paper reports a direct PVS-checked Treiber lock-freedom
   instantiation. The 2009 paper and this bundle generalize the method and
   supply completed queue cases; the unfinished legacy file does not erase or
   reproduce the separately published 2007 result. Because the 2007 full text
   is access-controlled, its exact theorem wording remains flagged for human
   confirmation in the screening ledger.

### Claim boundary imposed by the Colvin–Dongol lineage

The 2007 result defeats broad priority wording for a direct machine-checked
Treiber lock-freedom proof, while the 2009 artifact demonstrates an established
PVS methodology for machine-checked lock-freedom. Neither supplies an RC11
carrier, genuine weak CAS, separated scheduler/memory/primitive fairness, an
all-spurious execution, or candidate-style safety composition. The incomplete
`treiber.pvs` is negative artifact evidence about the 2009 bundle only; it is
not evidence against the 2007 publication's reported checked result.

Primary sources:
[Colvin and Dongol, *Verifying Lock-Freedom Using Well-Founded Orders*](https://doi.org/10.1007/978-3-540-75292-9_9)
and
[Colvin and Dongol, *A General Technique for Proving Lock-Freedom*](https://doi.org/10.1016/j.scico.2008.09.013).

## A06: RoboCop

### Exact Treiber benchmark boundary

The artifact contains the `03_treiber_stack` benchmark and reports the paper's
reference run as 7.817785 seconds with three locations, four relaxed accesses,
and two release/acquire accesses
([README, lines 121–146](data/artifacts/extracted/robocop-oopsla24-artifact.tar/artifact/README.md#L121-L146)).
Both `push` and `pop` call
`atomic_compare_exchange_strong_explicit`; there is no weak compare-exchange
call in the benchmark
([`lib.c`, lines 8–40](data/artifacts/extracted/robocop-oopsla24-artifact.tar/artifact/benchmarks/03_treiber_stack/lib.c#L8-L40)).

The audit reran that benchmark in a temporary Python 3.12 virtual environment
with `pycparser==3.0` and `z3-solver==5.0.0.0`. It exited successfully and
printed:

```text
[REPORT] benchmarks/03_treiber_stack/lib.c,13.731607s,3,4,2
```

The differing wall time is expected and the structural counts match the
artifact report. This reproduces automated RC20 robustness checking for the
strong-CAS Treiber input. It does not test operation termination, preserve
failed retry iterations as liveness evidence, or instantiate genuine weak
CAS.

A minimal reproduction from the extracted artifact directory is:

```bash
python3 -m venv /tmp/robocop-audit-venv
/tmp/robocop-audit-venv/bin/pip install \
  pycparser==3.0 z3-solver==5.0.0.0
PATH=/tmp/robocop-audit-venv/bin:$PATH \
  /tmp/robocop-audit-venv/bin/python -m robocop \
  benchmarks/03_treiber_stack/lib.c \
  benchmarks/03_treiber_stack/spec.txt
```

### Claim boundary

RoboCop is executable, direct relaxed-memory Treiber safety prior art. Its
artifact strengthens the evidence for PA45, but the input itself uses strong
CAS and the checked property is robustness. It therefore cannot subsume the
genuine-weak-CAS progress, primitive-justice, or all-spurious parts of the
candidate.

## A07: General-Purpose RCU Rocq development

### Mechanized-client inventory

The archived README says its RCU traversal specification is instantiated by
library verifications, then lists the Michael–Scott queue with code,
specification, and proof files
([README, lines 199–213](data/artifacts/extracted/jung-2025-rcu-artifact/pldi25-3-artifact/README.md#L199-L213))
and Harris-list variants with their code, specification, and proof files
([README, lines 215–229](data/artifacts/extracted/jung-2025-rcu-artifact/pldi25-3-artifact/README.md#L215-L229)).
The 156 extracted files contain zero pathname matches for `stack` and zero for
`treiber`.

The archive's `LICENSE` names several upstream `gpfsl-examples/stack/*` files
([lines 4–18](data/artifacts/extracted/jung-2025-rcu-artifact/pldi25-3-artifact/LICENSE#L4-L18)),
but those paths are absent from this archive and `_CoqProject`. Those license
references are not evidence of an archived Treiber client proof.

### Primitive semantics

The general language semantics has an exact CAS: `CasFailS` requires
`lit_neq`, whereas `CasSucS` requires `lit_eq`
([`lang.v`, lines 353–381](data/artifacts/extracted/jung-2025-rcu-artifact/pldi25-3-artifact/gpfsl/lang/lang.v#L353-L381)).
There is no compare-equal spurious branch in those rules.

### Claim boundary

The paper's Algorithm 1 and §3.1 work through an iRC11 Treiber-with-RCU safety
argument, but the archived Rocq source mechanizes RCU plus the queue/list
clients rather than that Treiber illustration. PA46 must therefore be called
paper-level Treiber safety adjacent to mechanized iRC11 RCU—not a
machine-checked Treiber theorem. Neither paper nor artifact supplies Treiber
liveness, genuine weak CAS, primitive justice, or an all-spurious execution.

## A08: CQS Coq/Iris source

### Inventory and paper-to-artifact boundary

The pinned `cqs-proofs` branch contains 1,203 regular files, including 33
Coq `.v` files under
[`formal-proofs/theories`](data/artifacts/extracted/cqs-proofs-970ef8c.tar/kotlinx.coroutines-970ef8c280dd8b934b3e89f78266e9b68b1a1290/formal-proofs/theories).
The checked code covers HeapLang implementations and safety specifications for
the concurrent linked list, infinite array, barriers, semaphores, and related
utilities. Repository-wide exact-term searches over those 33 Coq files found
no `fair`, `fairness`, `liveness`, `termination`, or `lock-free` occurrence.
No file path or source occurrence names the paper's blocking pool, modified
Treiber outer stack, or Appendix F.4 construction.

The paper's fair-synchronization progress argument and Treiber-derived outer
storage therefore exceed what is present in this pinned public proof branch.
This is an artifact-completeness finding about commit
`970ef8c280dd8b934b3e89f78266e9b68b1a1290`; it is not a claim that the
authors have no other development.

### Claim boundary

CQS is important fair-synchronizer and Treiber-construction prior art. Its
formal branch uses ordinary HeapLang CAS and supplies safety proofs, not
RC11 semantics, compare-equal weak-CAS failure, primitive justice, an
all-spurious separation, or a mechanized Treiber progress theorem. It narrows
the wording of the candidate without subsuming the full conjunction.

## A09: GenMC v0.6 source

### Safe archive audit

The pinned tar archive contains 4,254 regular files, 1,093 directories, and
one symbolic link. The link is the unsafe absolute target
`include/cassert -> /home/michalis/Documents/genmc-tool/include/assert.h`;
the generic extractor rejected it and wrote no A09 tree. Integrity was
verified with `--no-extract`, and the cited regular members were read directly
with Python's `tarfile` module and `tar -xOf`.

### Weak-CAS and Treiber boundary

In archive member `include/stdatomic.h`, lines 140--144 expose both strong and
weak compare-exchange macros. In `src/Execution.cpp`,
`visitAtomicCmpXchgInst` at lines 1412--1458 compares the returned value with
the expected value, stores exactly when equality holds, and never consults
`I.isWeak()`. Thus this pinned engine does not generate compare-equal
spurious failure. Both bundled Treiber variants,
`tests/correct/data-structures/treiber-stack/my_stack.c` and
`treiber-stack-dynamic/my_stack.c`, call
`atomic_compare_exchange_strong_explicit`.

GenMC is executable C11/RC11-family weak-memory model-checking prior art with a
Treiber regression benchmark. The relevant result is bounded safety/error
exploration, not a scheduler-fair termination or response-progress proof.
The pinned source therefore defeats broad “first weak-memory model checker
with Treiber” wording but supplies no genuine-weak-CAS Treiber theorem,
primitive justice, three-way fairness factorization, all-spurious witness, or
proof-assistant certificate.

## A10: Burrow Agda source

### Inventory and proof scope

The pinned commit `739a32764b6ebf74d0dec9d604e76919a85706f7`
contains 23 regular files, including 20 Agda modules. Its README maps the
development to axiomatic weak-memory executions, well-formedness lemmas,
generic mapping frameworks, and templates. The paper and source implement
proof infrastructure for graph-robustness-preserving mappings; the advertised
case study is x86 to Arm.

An exact repository-wide scan found no `Treiber`, `weak CAS`, `cas_weak`,
`fairness`, `liveness`, `termination`, `lock-free`, `response progress`, or
`all-spurious` term. The scan is a bounded statement about the pinned
`agda-burrow` repository; the separate `armed-proofs` case-study repository
was not silently treated as part of this archive.

### Claim boundary

Burrow is cutoff-eligible, proof-assistant-checked axiomatic weak-memory prior
art and materially strengthens the mechanization landscape. Its result is a
safety/refinement-style mapping theorem over execution graphs, not an
algorithm liveness theorem. It contains no explicit Treiber client,
compare-exchange result semantics, scheduler/memory/primitive fairness split,
weak-CAS justice, all-spurious separation, or response-progress conclusion.

## A11: Promising-ARM/RISC-V Coq supplement

### Model and independent-failure boundary

The 295-file supplement identifies Coq 8.8 as its proof-checking toolchain and
maps its checked results to the Global-Promising, axiomatic, certification,
and promise-computation modules
([README, lines 1–75](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/coq/README.md#L1-L75)).
Its assembly-like language represents load/store exclusivity with a Boolean
instruction flag
([`Lang.v`, lines 127–141](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/coq/src/lib/Lang.v#L127-L141)).
Most importantly, `write_failure` requires only that this flag be true: it
returns failure value 1 and clears the exclusive bank, without a premise about
an intervening write, a value mismatch, or another thread
([`Promising.v`, lines 895–912](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/coq/src/promising/Promising.v#L895-L912)).
`step_write_failure` exposes that rule as an ordinary local step
([`Promising.v`, lines 948–963](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/coq/src/promising/Promising.v#L948-L963)).

This is direct mechanized prior art for an independently failing
store-exclusive operation in an ARMv8/RISC-V operational model. It is not
itself a C11 `compare_exchange_weak` specification or a fairness condition
requiring eventual exclusive-store success.

### Treiber benchmark and theorem boundary

The supplement separately includes both C++ and Rust Treiber examples. The
C++ `try_push` and `try_pop` are single-attempt operations using
`compare_exchange_strong`
([`STC/stack.cpp`, lines 38–64](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/examples/STC/stack.cpp#L38-L64)).
The Rust variants likewise call `compare_exchange`, rather than
`compare_exchange_weak`
([`STR/stack.rs`, lines 49–79](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/examples/STR/stack.rs#L49-L79)).
The C++ driver has three threads, bounded allocation, and loop counts supplied
as finite parameters
([`STC/stack.cpp`, lines 6–19 and 67–164](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/examples/STC/stack.cpp#L6-L164));
the archive contains finite generated litmus instances used by the executable
exploration reported in the paper.

The Coq README lists model equivalence, certification soundness/completeness,
promise computation, and RISC-V deadlock freedom as the checked results
([README, lines 42–75](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/coq/README.md#L42-L75)).
The named deadlock-freedom theorem assumes a well-formed, certifiable machine
and concludes that some finite sequence reaches a state with no outstanding
promises
([`CertifyProgressRiscV.v`, lines 1350–1358](data/artifacts/extracted/promising-arm-riscv-supp/supplementary_material/coq/src/lcertify/CertifyProgressRiscV.v#L1350-L1358)).
It is a machine-model certification result, not a Treiber operation-response
or lock-freedom theorem. An exact scan of the 25 project Coq modules found no
`Treiber` or `stack` occurrence; the Treiber examples are not Coq client
proofs.

### Claim boundary

Promising-ARM/RISC-V is the closest audited hardware-model predecessor for the
candidate's genuine-spurious primitive dimension: it mechanizes an
unconditionally available exclusive-store failure step and evaluates finite
Treiber examples. It therefore defeats broad wording about first combining a
mechanized weak-memory model, independent exclusive failure, and a Treiber
benchmark. Its Treiber code uses strong compare-exchange, its checked theorems
concern model equivalence and certification, and it supplies no primitive
justice, all-spurious separation theorem, unbounded response progress, or
mechanized Treiber safety-and-liveness composition.

## Cross-artifact comparison of the original five

| Dimension | FOS | Lilo v3 | Lawyer | Spirea | Colvin–Dongol PVS |
|---|---|---|---|---|---|
| Mechanization | Coq | Coq | Rocq/Iris/Trillium | Coq/Iris/Perennial | PVS |
| Closest checked algorithm | Weak-memory ticket lock | Treiber and elimination stacks | CAS counter and ticket-lock client | Durable Treiber and Michael–Scott queue | Michael–Scott and bounded-array queues; direct Treiber only in the separate 2007 publication |
| Treiber primitive | No Treiber case | Strong CAS | No Treiber case | Strong/exact-match CAS | Strong CAS in incomplete legacy theory |
| Weak-CAS primitive | Present, fair, unused | Present, fair, unused by Treiber | Absent in screened source | Absent in screened source | Absent in screened source |
| Memory setting of closest case | Operational fair weak-memory module; load/store/FAA | Single global heap/interleaving | Single shared HeapLang heap/interleaving | Operational release/acquire weak persistent memory | Atomic global-state interleaving |
| Primitive fairness separated from scheduler/memory fairness | Expressible as a separate fairness event; no integrated independence witness | Co-located mechanism; no Treiber use or independence witness | No weak-CAS primitive-fairness dimension | No liveness-fairness dimension | No weak-CAS primitive-fairness dimension |
| Positive result closest to target | Fair ticket-lock/client refinement | Termination-guaranteeing Treiber specifications and finite client | Closed-program termination for strong-CAS counter | Thread/crash safety and null recovery only | Machine-checked queue lock-freedom; separately reported 2007 PVS Treiber lock-freedom |
| Integrated all-spurious Treiber/RC11 separation | Not found | Not found | Not found | Not found | Not found |
| Unbounded system-wide response theorem for weak-CAS Treiber | Not found | Not found | Not found | Not found | Not found |

The later artifacts add six distinct boundaries:

| Dimension | RoboCop | General-Purpose RCU | CQS | GenMC v0.6 | Burrow | Promising-ARM/RISC-V |
|---|---|---|---|---|---|---|
| Checked artifact | Automated RC20 robustness tool | Rocq/Iris iRC11 RCU, mutex, queue, and list developments | Coq/Iris safety development for CQS components | Executable weak-memory model checker | Agda axiomatic weak-memory mapping framework | Coq ARMv8/RISC-V operational/axiomatic equivalence and certification metatheory |
| Treiber presence | Executable benchmark using `compare_exchange_strong` | Paper illustration only; no Treiber file in the archived source | Paper-level modified outer stack; no matching proof file in pinned branch | Bundled regression benchmarks using strong CAS | None | Finite C++/Rust executable examples, separate from the Coq modules |
| CAS failure | Exact/mismatch-only for the benchmark | `CasFailS` requires inequality | Ordinary HeapLang equality-guarded CAS | Engine success determined by equality; weak flag unused | No client-level CAS result semantics | Independent exclusive-store failure in the Coq model; Treiber source uses strong CAS |
| Liveness result | None | None | Paper-level fair synchronization; not mechanized in audited branch | None; bounded safety/error exploration | None; graph-robustness/mapping proof | RISC-V certification/deadlock freedom, not Treiber response progress |
| Full candidate conjunction | Not found | Not found | Not found | Not found | Not found | Not found |

## Reproducibility and negative-search limits

- Every source citation above was checked against the extracted file and line
  range, and every linked local path existed at audit time.
- The Zenodo DOI links and author PDFs returned HTTP 200 on 2026-07-31. Each
  publication DOI resolved to the expected publisher page; automated requests
  to ACM Digital Library then received HTTP 403, so resolution, not ACM page
  body retrieval, is what was validated for the ACM DOI links.
- Repository-wide negative searches establish absence only for the recorded
  source trees, artifact versions, extensions, and terms. They are not evidence
  about unpublished branches, later releases, differently named definitions,
  or results hidden behind terminology not covered by the scans.
- Archive integrity and source presence are independently reproducible from
  the commands above. Proof-kernel reproduction remains a separate task using
  each artifact's pinned or documented toolchain.

## Audit conclusion

The artifacts force a narrow claim boundary:

- FOS predates this project and already supplies a formal fair weak-CAS
  mechanism and a mechanized weak-memory fairness framework.
- Lilo predates this project and already supplies a machine-checked strong-CAS
  Treiber liveness result. It is the strongest artifact-level threat because
  it co-locates unused fair weak CAS.
- Lawyer already supplies machine-checked strong-CAS retry-loop and fair
  closed-program termination results.
- Spirea already supplies a mechanized durable Treiber safety case under weak
  persistent memory, but explicitly not a linearizability or liveness result.
- The Colvin–Dongol lineage already reports a direct 2007 PVS Treiber
  lock-freedom result and supplies completed 2009 PVS queue proof families;
  the latter archive's legacy Treiber theory is not itself complete.
- RoboCop reproducibly checks RC20 robustness for a strong-CAS Treiber
  benchmark; this is safety, not retry-loop liveness.
- The General-Purpose RCU archive mechanizes iRC11 RCU and queue/list clients,
  while the paper-level Treiber-with-RCU example is not present as an archived
  Rocq development.
- CQS provides checked synchronization-safety components and a paper-level
  fair/Treiber-derived construction, but the pinned public proof branch lacks
  its named outer-stack files and any mechanized progress development.
- GenMC v0.6 already supplies weak-memory model checking with Treiber
  regression inputs, but its audited engine treats compare-exchange as exact,
  its Treiber inputs use strong CAS, and it checks no positive progress
  property.
- Burrow already supplies an Agda framework for axiomatic weak-memory mapping
  proofs, but its pinned source and x86-to-Arm case establish graph robustness,
  not a concurrent-object liveness or weak-CAS justice result.
- Promising-ARM/RISC-V already mechanizes an independently failing
  store-exclusive step and includes finite Treiber exploration inputs, but its
  Treiber sources use strong compare-exchange and its Coq theorems establish
  model metatheory rather than object safety or response progress.

No screened artifact connects genuinely weak CAS, Treiber, RC11-valid finite
prefixes, distinct scheduler/memory/primitive fairness, an integrated coherent
all-spurious independence witness, finite-prefix linearizability, and
unbounded system-wide response progress. That is a finding of this bounded
artifact screen, not a proof of worldwide priority. The candidate priority
claim remains contingent on the remaining literature search and independent
expert review.
