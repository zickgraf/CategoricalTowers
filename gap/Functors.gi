# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#

BindGlobal( "FUNCTOR_CATEGORIES", rec( QQ := HomalgFieldOfRationals( ) ) );

##
InstallMethod( ConvertToCellInFunctorCategory,
    [ IsQuiverRepresentation ],
    
  function ( rep )
    local reps, A, A_oid, k, dims, matrices, F;
    
    reps := CapCategory( rep );
    
    A := AlgebraOfCategory( reps );
    
    A_oid := Algebroid( A );
    
    k := CommutativeRingOfLinearCategory( A_oid );
    
    dims := DimensionVector( rep );
    
    matrices := List( MatricesOfRepresentation( rep ),
      mat -> HomalgMatrix(
                RowsOfMatrix( mat ),
                  DimensionsMat( mat )[ 1 ],
                    DimensionsMat( mat )[ 2 ], k ) );
    
    F := AsObjectInFunctorCategory( A_oid, dims, matrices );
    
    SetConvertToCellInCategoryOfQuiverRepresentations( F, rep );
    
    return F;
    
end );

##
InstallMethod( ConvertToCellInFunctorCategory,
          [ IsQuiverRepresentationHomomorphism ],
          
  function ( phi )
    local reps, A, A_oid, k, e, F, G, eta;
    
    reps := CapCategory( phi );
    
    A := AlgebraOfCategory( reps );
    
    A_oid := Algebroid( A );
    
    k := CommutativeRingOfLinearCategory( A_oid );
    
    e := List( MatricesOfRepresentationHomomorphism( phi ),
          mat -> HomalgMatrix(
                    RowsOfMatrix( mat ),
                      DimensionsMat( mat )[ 1 ],
                        DimensionsMat( mat )[ 2 ], k ) );
    
    F := ConvertToCellInFunctorCategory( Source( phi ) );
    G := ConvertToCellInFunctorCategory( Range( phi ) );
    
    eta := AsMorphismInFunctorCategory( F, e, G );
    
    SetConvertToCellInCategoryOfQuiverRepresentations( eta, phi );
    
    return eta;
    
end );

##
InstallMethod( IsomorphismFromCategoryOfQuiverRepresentations,
        [ IsFunctorCategory ],
        
  function ( functors )
    local B, A, reps, name, I;
    
    B := Source( functors );
    
    A := UnderlyingQuiverAlgebra( B );
    
    reps := CategoryOfQuiverRepresentations( A );
    
    name := Concatenation( "Isomorphism functor: ", Name( reps ), " -> ", Name( functors ) );
    
    I := CapFunctor( name, reps, functors );
    
    AddObjectFunction( I,
      rep -> ConvertToCellInFunctorCategory( rep )
    );
    
    AddMorphismFunction( I,
      { S, phi, R } -> ConvertToCellInFunctorCategory( phi )
    );
    
    return I;
    
end );

##
InstallMethod( ConvertToCellInCategoryOfQuiverRepresentations,
          [ IsObjectInFunctorCategory ],
          
  function ( F )
    local B, A, k, dims, matrices, rep;
    
    B := Source( F );
    
    A := UnderlyingQuiverAlgebra( B );
    
    k := LeftActingDomain( A );
    
    dims := List( ValuesOnAllObjects( F ), Dimension );
    
    matrices := List( ValuesOnAllGeneratingMorphisms( F ), UnderlyingMatrix );
    
    matrices := List( matrices, m -> MatrixByRows(
                                        k,
                                        [ NrRows( m ), NrColumns( m ) ],
                                        EntriesOfHomalgMatrixAsListList( m )
                                      )
                    );
    
    rep := QuiverRepresentation( A, dims, matrices );
    
    SetConvertToCellInFunctorCategory( rep, F );
    
    return rep;
    
end );

##
InstallMethod( ConvertToCellInCategoryOfQuiverRepresentations,
          [ IsMorphismInFunctorCategory ],
          
  function ( eta )
    local B, A, k, matrices, S, R, phi;
    
    B := Source( CapCategory( eta ) );
    
    A := UnderlyingQuiverAlgebra( B );
    
    k := LeftActingDomain( A );
    
    matrices := List( ValuesOnAllObjects( eta ), UnderlyingMatrix );
    
    matrices := List( matrices, m -> MatrixByRows(
                                        k,
                                        [ NrRows( m ), NrColumns( m ) ],
                                        EntriesOfHomalgMatrixAsListList( m )
                                      )
                    );
    
    S := ConvertToCellInCategoryOfQuiverRepresentations( Source( eta ) );
    
    R := ConvertToCellInCategoryOfQuiverRepresentations( Range( eta ) );
    
    phi := QuiverRepresentationHomomorphism( S, R, matrices );
    
    SetConvertToCellInFunctorCategory( phi, eta );
    
    return phi;
    
end );

##
InstallMethod( IsomorphismOntoCategoryOfQuiverRepresentations,
        [ IsFunctorCategory ],
        
  function ( functors )
    local B, A, reps, name, J;
    
    B := Source( functors );
    
    A := UnderlyingQuiverAlgebra( B );
    
    reps := CategoryOfQuiverRepresentations( A );
    
    name := Concatenation( "Isomorphism functor: ", Name( functors ), " -> ", Name( reps ) );
    
    J := CapFunctor( name, functors, reps );
    
    AddObjectFunction( J,
      F -> ConvertToCellInCategoryOfQuiverRepresentations( F )
    );
    
    AddMorphismFunction( J,
      { F, eta, G } -> ConvertToCellInCategoryOfQuiverRepresentations( eta )
    );
    
    return J;
    
end );

##
InstallMethod( NerveTruncatedInDegree2,
        [ IsFpCategory ],
        
  function ( B )
    
    return AsObjectInFunctorCategory( NerveTruncatedInDegree2AsFunctor( B ) );
    
end );

##
InstallMethod( YonedaEmbedding,
        [ IsCapCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    local A, PSh, B_op, objs, mors, name, Yoneda;
    
    A := UnderlyingQuiverAlgebra( B );
    
    if not IsFiniteDimensional( A ) then
        
        Error( "The underlying quiver algebra should be finite dimensional!\n" );
        
    fi;
    
    PSh := PreSheaves( B );
    
    B_op := Source( PSh );
    
    objs := SetOfObjects( B );
    
    mors := SetOfGeneratingMorphisms( B );
    
    name := "Yoneda embedding functor";
    
    Yoneda := CapFunctor( name, B, PSh );
    
    AddObjectFunction( Yoneda,
      function ( obj )
        local Yo;
        
        Yo := AsObjectInFunctorCategory( B_op,
                      List( objs, o -> HomStructure( o, obj ) ),
                      List( mors, m -> HomStructure( m, obj ) ) );
        
        SetIsProjective( Yo, true );
        
        return Yo;
        
    end );
    
    AddMorphismFunction( Yoneda,
      function ( s, mor, r )
        
        return AsMorphismInFunctorCategory(
                       s,
                       List( objs, o -> HomStructure( o, mor ) ),
                       r );
        
    end );
    
    return Yoneda;
    
end );

##
InstallMethod( YonedaProjection,
        [ IsFpCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    local mu;
    
    mu := AsMorphismInFunctorCategory( YonedaProjectionAsNaturalEpimorphism( B ) );
    
    Assert( 3, IsEpimorphism( mu ) );
    SetIsEpimorphism( mu, true );
    
    return mu;
    
end );

##
InstallMethod( YonedaComposition,
        [ IsFpCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    local mu;
    
    mu := AsMorphismInFunctorCategory( YonedaCompositionAsNaturalEpimorphism( B ) );
    
    Assert( 3, IsEpimorphism( mu ) );
    SetIsEpimorphism( mu, true );
    
    return mu;
    
end );

##
InstallMethod( YonedaFibration,
        [ IsFpCategory and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( B )
    
    return AsMorphismInFunctorCategory( YonedaFibrationAsNaturalTransformation( B ) );
    
end );

##
InstallMethodForCompilerForCAP( SievesOfPathsToTruth,
        [ IsFunctorCategory, IsMorphismInFunctorCategory ],
        
  function ( Hom, iota ) ## ι: Q ↪ P
    local Q, P, Bop, B_0, B, H, D, emb, Omega, OmegaH, s, Y,
          truth_values, bool, paths_to_truth;
    
    ## B^op
    Bop := Source( Hom );
    
    ## B^op → H
    Q := Source( iota );
    P := Range( iota );
    
    B_0 := SetOfObjects( Bop );
    
    B := OppositeFpCategory( Bop );
    
    H := RangeCategoryOfHomomorphismStructure( B );
    
    D := DistinguishedObjectOfHomomorphismStructure( B );
    
    ## The natural transformation c ↦ ( Sieves(c) ↪ Hom(Hom(-, c), Ω) )
    emb := AsMorphismInFunctorCategory( EmbeddingOfSieveFunctor( B ) );
    
    Omega := Source( emb );
    
    OmegaH := SubobjectClassifier( H );
    
    ## The source fibration is a natrual morphism from the Yoneda functor to the constant functor of 0-cells
    ## Hom(-, c) → B_0:
    s := YonedaFibration( B );
    
    ## The Yoneda functor B → H, c ↦ Hom(-, c), ψ ↦ Hom(-, ψ), where
    ## Hom(-, c) := ⊔_{a ∈ B} Hom(a, c),
    ## Hom(-, ψ) := ⊔_{a ∈ B} Hom(id_a, ψ):
    Y := Source( s );
    
    ## Truth values of Ω
    truth_values := [ TruthMorphismOfTrue( H )( 1 ), TruthMorphismOfFalse( H )( 1 ) ];
    
    ## true ↦ 1, false ↦ 2
    bool :=
      function ( b )
        if b then
            return truth_values[1];
        else
            return truth_values[2];
        fi;
    end;
    
    ## the sieve of all f ∈ Hom(-, c), such that x P(f) ∈ Q(a) ⊆ P(a), where a = Source(f):
    paths_to_truth :=
      function ( c, x )
        local hom_c, s_c, emb_c, sieve;
        
        ## Hom(-, c) := ⊔_{a ∈ B} Hom(a, c)
        hom_c := Y( OppositePath( UnderlyingVertex( c ) ) / B );
        
        ## Hom(-, c) → B_0
        s_c := s( OppositePath( UnderlyingVertex( c ) ) / B );
        
        ## Sieves(c) ↪ Hom(Hom(-, c), Ω)
        emb_c := emb( c );
        
        ## Sieve(x) ↪ Hom(-, c) as an "element" D → Sieves(c):
        return LiftAlongMonomorphism(
                       ## Sieves(c) ↪ Hom(Hom(-, c), Ω)
                       emb_c,
                       ## Sieve(x) ↪ Hom(-, c) as an "element" D → Hom(Hom(-, c), Ω):
                       InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure(
                               ## χ: Hom(-, c) → Ω:
                               MapOfFinSets(
                                       hom_c,
                                       List( List( hom_c, f ->
                                               ## Is x P(f) ∈ Q(a) ⊆ P(a), where a = Source(f)?
                                               IsLiftableAlongMonomorphism(
                                                       ## ι_c: Q(c) ↪ P(c):
                                                       iota( c ),
                                                       ## x P(f) ∈ P(a), where a = Source(f):
                                                       PreCompose(
                                                               ## x ∈ P(c):
                                                               x,
                                                               ## P(f): P(c) → P(a):
                                                               P(
                                                                 ## f: a → c, where a = Source(f):
                                                                 InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism(
                                                                         B_0[s_c( f )],
                                                                         c,
                                                                         MapOfFinSets( D, [ f ], hom_c ) ) ) ) ) ), bool ),
                                       OmegaH ) ) )(1);
        
    end;
    
    ## χ: P → Ω
    return AsMorphismInFunctorCategory(
                   P,
                   List( B_0,
                         c -> MapOfFinSets(
                                 P( c ),
                                 List( P( c ), x -> paths_to_truth( c, MapOfFinSets( D, [ x ], P( c ) ) ) ),
                                 Omega( c ) ) ),
                   Omega );
    
end );

##
InstallMethod( SievesOfPathsToTruth,
        [ IsMorphismInFunctorCategory and IsMonomorphism ],
        
  function ( iota )
    
    return SievesOfPathsToTruth( CapCategory( iota ), iota );
    
end );
