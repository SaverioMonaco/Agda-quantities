# Agda-quantities
Type-safe physical computations in Agda.

---
## Physical Quantity as Agda type:
![scheme](/imgs/schema.svg)

---
## Tutorial:
Check out the two `.agda` files in `/src/Quantities/Manuals/` on how to use this library:
- [Units.agda](/src/Quantities/Manuals/Units.agda) : with examples on how to use the Units type.
- [Physical.agda](/src/Quantities/Manuals/Physical.agda) : with examples on how to use the Physical Quantities (PQ) type.

---
## How to run it:
This library depends on the [Agda-stdlib](https://github.com/agda/agda-stdlib), in particular it was tested with `agda-stdlib-1.7.1`.

1. Clone the repository to a directory `$REPODIR`
```bash
git clone https://github.com/SaverioMonaco/Agda-quantities.git $REPODIR
```

2. Locate your `$AGDA_DIR`, which for unix systems defaults to `~/.agda`

3. Append to `$AGDA_DIR/libraries` the following content:
```bash
$REPODIR/Agda-quantities/Quantities.agda-lib
```
4. Append to `$AGDA_DIR/defaults` the following content:
```bash
Quantities
```
5. If everything has been linked correctly, you should be able to use the Quantities library anywhere, to test it load the following line in a `.agda` file:
```agda
open import Quantities.Quantities
```


For more information: [package-system](https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html)

---
## Resources:
* Some of my personal notes [GitHub repo](https://github.com/SaverioMonaco/TypeTheory)
* Library Management [agda.readthedocs.io](https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html)
* Library for type-safe physical computations and unit conversions in Idris [GitHub repo](https://github.com/timjb/quantities)
* Agda-stdlib [GitHub repo](https://github.com/agda/agda-stdlib)