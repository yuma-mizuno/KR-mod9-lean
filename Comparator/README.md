# Independent specification

- [KanadeRussell.lean](KanadeRussell.lean) states the definitions and 16 targets
  independently of the production library. Each target has one intentional
  `sorry`; this specification is not imported by the proof library.
- [Solution.lean](Solution.lean) proves all 16 targets with exactly the same
  types using the production library. It contains no `sorry`.
- [check_statements.py](check_statements.py) checks finite truncations using
  Python's standard library. These numerical checks do not constitute proofs.

Run from the repository root:

```sh
lake build KanadeRussell
python scripts/check-comparator.py
lake env lean Comparator/Solution.lean
python scripts/audit-axioms.py
python Comparator/check_statements.py
```

To elaborate the independent specification itself, run `lake build Comparator`.
The 16 `sorry` warnings from that command are intentional. Production proofs
are checked separately and may depend only on `propext`, `Classical.choice`,
and `Quot.sound`.
