# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Reading the implementation part of the package.
#

ReadPackage( "Algebroids", "gap/QuiverRows.gi" );

ReadPackage( "Algebroids", "gap/precompiled_categories/CategoryFromNerveDataPrecompiled.gi" );
ReadPackage( "Algebroids", "gap/precompiled_categories/CategoryFromNerveDataHomStructureOnMorphismsPrecompiled.gi" );

ReadPackage( "Algebroids", "gap/precompiled_categories/CategoryFromDataTablesPrecompiled.gi" );

ReadPackage( "Algebroids", "gap/precompiled_categories/AdditiveClosureOfAlgebroidOfFiniteDimensionalQuiverAlgebraOfRightQuiverOverFieldPrecompiled.gi" );
ReadPackage( "Algebroids", "gap/precompiled_categories/AdditiveClosureOfAlgebroidOfFiniteDimensionalQuiverAlgebraOfRightQuiverOverZPrecompiled.gi" );

ReadPackage( "Algebroids", "gap/precompiled_categories/AdelmanCategoryOfAdditiveClosureOfAlgebroidOfFiniteDimensionalQuiverAlgebraOfRightQuiverOverFieldPrecompiled.gi" );
ReadPackage( "Algebroids", "gap/precompiled_categories/AdelmanCategoryOfAdditiveClosureOfAlgebroidOfFiniteDimensionalQuiverAlgebraOfRightQuiverOverZPrecompiled.gi" );

ReadPackage( "Algebroids", "gap/FpCategories.gi");
ReadPackage( "Algebroids", "gap/Algebroids.gi");
ReadPackage( "Algebroids", "gap/QPA2.gi");
ReadPackage( "Algebroids", "gap/Functors.gi");
ReadPackage( "Algebroids", "gap/CategoryFromNerveData.gi");
ReadPackage( "Algebroids", "gap/CategoryFromDataTables.gi");
ReadPackage( "Algebroids", "gap/CategoryOfAlgebroids.gi");
ReadPackage( "Algebroids", "gap/Bialgebroids.gi");
ReadPackage( "Algebroids", "gap/SimplicialCategory.gi");
ReadPackage( "Algebroids", "gap/Tools.gi");

if IsPackageMarkedForLoading( "JuliaInterface", ">= 0.2" ) then
    ReadPackage( "Algebroids", "gap/Julia.gi" );
fi;
