#! @Chunk DiscreteSkeletalCategory

#! @Example
LoadPackage( "Locales" );
#! true
D := DiscreteSkeletalCategory( "IsInt" );
#! DiscreteSkeletalCategory( "IsInt" )
Display( D );
#! A CAP category with name DiscreteSkeletalCategory( "IsInt" ):
#! 
#! 11 primitive operations were used to derive 74 operations for this category
#! which algorithmically
#! * IsPosetCategory
#! * IsEquippedWithHomomorphismStructure
#! and furthermore mathematically
#! * IsDiscreteCategory
#! * IsSkeletalCategory
one := 1 / D;
#! <An object in DiscreteSkeletalCategory( "IsInt" )>
Display( one );
#! 1
#!
#! An object in DiscreteSkeletalCategory( "IsInt" ) given by the above data
IsWellDefined( one );
#! true
IsWellDefined( "1" / D );
#! false
two := 2 / D;
#! <An object in DiscreteSkeletalCategory( "IsInt" )>
id_one := IdentityMorphism( one );
#! <An identity morphism in DiscreteSkeletalCategory( "IsInt" )>
MorphismDatum( id_one );
#! fail
IsOne( PreCompose( id_one, id_one ) );
#! true
IsOne( UniqueMorphism( one, one ) );
#! true
IsWellDefined( UniqueMorphism( one, two ) );
#! false
HomStructure( one, one );
#! <(⊤)>
HomStructure( one, two );
#! <(⊥)>
HomStructure( two, one );
#! <(⊥)>
#! @EndExample