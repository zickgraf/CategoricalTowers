# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Implementations
#

##
InstallMethod( DefiningTripleOfAQuiver,
        "for a quiver",
        [ IsQuiver ],
        
  function( q )
    local vertices, arrows;
    
    vertices := Vertices( q );
    arrows := Arrows( q );
    
    return Immutable(
                   Triple( Length( vertices ),
                           Length( arrows ),
                           List( arrows, m -> Pair( -1 + SafePosition( vertices, Source( m ) ), -1 + SafePosition( vertices, Range( m ) ) ) ) ) );
    
end );

##
InstallMethod( IndicesOfGeneratingMorphismsFromHomStructure,
        "for a finite category",
        [ IsCapCategory and IsFinite ],
        
  function( C )
    local sFinSets, C0, N0, D00, N0N0, p21, p22, C1, T, st, mors;
    
    sFinSets := RangeCategoryOfHomomorphismStructure( C );
    
    ## sFinSets must be the category skeletal finite sets
    Assert( 0, IsCategoryOfSkeletalFinSets( sFinSets ) );
    
    C0 := SetOfObjects( C );
    N0 := FinSet( sFinSets, Length( C0 ) );
    
    D00 := [ N0, N0 ];
    
    ## N0 × N0 -> N0
    p21 := ProjectionInFactorOfDirectProduct( sFinSets, D00, 1 );
    p22 := ProjectionInFactorOfDirectProduct( sFinSets, D00, 2 );
    
    C1 := List( DirectProduct( sFinSets, D00 ), i ->
                HomomorphismStructureOnObjects( C,
                        C0[1 + AsList( p21 )[1 + i]],
                        C0[1 + AsList( p22 )[1 + i]] ) );
    
    T := DistinguishedObjectOfHomomorphismStructure( C );
    
    st := List( DefiningTripleOfUnderlyingQuiver( C )[3], pair ->
                UniversalMorphismIntoDirectProduct( sFinSets,
                        D00,
                        T,
                        [ MapOfFinSets( sFinSets, T, [ pair[1] ], N0 ),
                          MapOfFinSets( sFinSets, T, [ pair[2] ], N0 ) ] ) );
    
    mors := SetOfGeneratingMorphisms( C );
    
    return List( [ 1 .. Length( st ) ], i ->
                 Sum( C1{[ 1 .. AsList( st[i] )[1 + 0] ]}, Length ) +
                 AsList( InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( C, mors[i] ) )[1 + 0] );
    
end );

##
InstallMethod( OppositeFiniteCategory,
        "for a finite category",
        [ IsCapCategory and IsFinite ],
        
  function( C )
    local C_op, defining_triple;
    
    C_op := Opposite( C );
    
    SetIsFinite( C_op, true );
    
    SetSetOfObjects( C_op,
            List( SetOfObjects( C ), Opposite ) );
    
    SetSetOfGeneratingMorphisms( C_op,
            List( SetOfGeneratingMorphisms( C ), Opposite ) );
    
    defining_triple := DefiningTripleOfUnderlyingQuiver( C );
    
    defining_triple := Triple( defining_triple[1],
                               defining_triple[2],
                               List( defining_triple[3], a -> Pair( a[2], a[1] ) ) );
    
    SetDefiningTripleOfUnderlyingQuiver( C_op, defining_triple );
    
    return C_op;
    
end );
