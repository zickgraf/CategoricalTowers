# SPDX-License-Identifier: GPL-2.0-or-later
# FiniteCocompletions: Finite (co)product/(co)limit (co)completions
#
# Implementations
#

##
InstallMethod( EnrichmentSpecificFiniteStrictCoproductCocompletion,
        "for a category",
        [ IsCapCategory ],
        
  function( C )
    
    if not HasRangeCategoryOfHomomorphismStructure( C ) then
        Error( "the category `C` has no RangeCategoryOfHomomorphismStructure\n" );
    fi;
    
    return EnrichmentSpecificFiniteStrictCoproductCocompletion( C, RangeCategoryOfHomomorphismStructure( C ) );
    
end );

##
InstallMethod( TensorizeObjectWithObjectInRangeCategoryOfHomomorphismStructure,
        "for an object in a cocartesian category and an object in the its range category of the homomorphism structure",
        [ IsCapCategoryObject, IsCapCategoryObject ],
        
  function( c, h )
    local UC;
    
    UC := EnrichmentSpecificFiniteStrictCoproductCocompletion( CapCategory( c ) );
    
    return TensorizeObjectWithObjectInRangeCategoryOfHomomorphismStructure( RangeCategoryOfHomomorphismStructure( UC ), UC, c, h );
    
end );

##
InstallMethod( TensorizeObjectWithMorphismInRangeCategoryOfHomomorphismStructure,
        "an object in a cocartesian category and a morphism in its range category of the homomorphism structure",
        [ IsCapCategoryObject, IsCapCategoryMorphism ],
        
  function( c, nu )
    local UC, H;
    
    UC := EnrichmentSpecificFiniteStrictCoproductCocompletion( CapCategory( c ) );
    H := RangeCategoryOfHomomorphismStructure( UC );
    
    return TensorizeObjectWithMorphismInRangeCategoryOfHomomorphismStructure( H, UC,
                   TensorizeObjectWithObjectInRangeCategoryOfHomomorphismStructure( H, UC, c, Source( nu ) ),
                   c,
                   nu,
                   TensorizeObjectWithObjectInRangeCategoryOfHomomorphismStructure( H, UC, c, Range( nu ) ) );
    
end );

##
InstallMethod( TensorizeMorphismWithObjectInRangeCategoryOfHomomorphismStructure,
        "for a morphism in a cocartesian category and an object in its range category of the homomorphism structure",
        [ IsCapCategoryMorphism, IsCapCategoryObject ],
        
  function( phi, h )
    local UC, H;
    
    UC := EnrichmentSpecificFiniteStrictCoproductCocompletion( CapCategory( phi ) );
    H := RangeCategoryOfHomomorphismStructure( UC );
    
    return TensorizeMorphismWithObjectInRangeCategoryOfHomomorphismStructure( H, UC,
                   TensorizeObjectWithObjectInRangeCategoryOfHomomorphismStructure( H, UC, Source( phi ), h ),
                   phi,
                   h,
                   TensorizeObjectWithObjectInRangeCategoryOfHomomorphismStructure( H, UC, Range( phi ), h ) );
    
end );
