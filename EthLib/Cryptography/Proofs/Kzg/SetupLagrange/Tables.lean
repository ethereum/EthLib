module

public import EthLib.Cryptography.Kzg.TrustedSetupData
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checker
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableA
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableB0
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableB1
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableB2
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableB3
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableL
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Data.TableM

/-!
# Proofs: the four tables of the setup check

The checks of the three rounds read four tables of affine points.

- `M` holds the decoded monomial points, and `L` the decoded Lagrange points in file order.
- `A` and `B` hold the outputs of the first two rounds.

`lake exe gen-setup-tables` writes their entries, in the modules that this file imports.

The proofs do not trust the tables: a wrong entry only makes a kernel check fail.

The file also exports the strings of the embedded setup, which the decoding checks read.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

/-- The decoded monomial points. -/
noncomputable def tableM : Table := entryAt tableMData

/-- The outputs of the first round. -/
noncomputable def tableA : Table := entryAt tableAData

/-- The outputs of the second round. -/
noncomputable def tableB : Table := fun n =>
  entryAt (#[tableBData0, tableBData1, tableBData2, tableBData3].getD (n / 1024) #[]) (n % 1024)

/-- The decoded Lagrange points, in file order. -/
noncomputable def tableL : Table := entryAt tableLData

end EthLib.Cryptography.Kzg.SetupLagrange
