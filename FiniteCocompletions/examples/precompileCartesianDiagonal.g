LoadPackage( "FunctorCategories", false );
#! true

LoadPackage( "CompilerForCAP", ">= 2022.09-02", false );
#! true

ReadPackageOnce( "FinSetsForCAP", "gap/CompilerLogic.gi" );
#! true

ReadPackageOnce( "Algebroids", "gap/CompilerLogic.gi" );
#! true

ReadPackageOnce( "FiniteCocompletions", "gap/CompilerLogic.gi" );
#! true

ReadPackageOnce( "FunctorCategories", "gap/CompilerLogic.gi" );
#! true

PC := FiniteStrictProductCompletion( CategoryFromDataTables( FreeCategory( RightQuiver( "Q(a)[]" ) : range_of_HomStructure := CategoryOfSkeletalFinSets( : no_precompiled_code := true ) ) : no_precompiled_code := true ) : no_precompiled_code := true );

a := PC.a;

aa := DirectProduct( PC, [ a, a ] );
    
delta := MorphismsOfExternalHom( PC, a, aa )[1];

dummy := DummyCategory( rec(
    list_of_operations_to_install := [
        "PreCompose",
        "IdentityMorphism",
        "DirectProduct",
        "ProjectionInFactorOfDirectProductWithGivenDirectProduct",
        "UniversalMorphismIntoDirectProductWithGivenDirectProduct"
    ],
    properties := [ "IsCartesianCategory" ],
) );

C := UnderlyingCategory( PC );

C_a := C.a;

func :=
  function( dummy, dummy_a, dummy_aa )
    local delta, object_function, morphism_function, universal_functor;
    
    # express delta in terms of the unique object C_a of C
    delta := MorphismConstructor( PC,
                     ObjectConstructor( PC, Pair( 1, [ C_a ] ) ), # a
                     Pair( [ 0, 0 ], [ IdentityMorphism( C, C_a ), IdentityMorphism( C, C_a ) ] ),
                     ObjectConstructor( PC, Pair( 2, [ C_a, C_a ] ) ) ); # aa
    
    # C → PC
    #coyoneda_embedding := CoYonedaEmbeddingOfUnderlyingCategoryData( PC );
    
    # PC ⭇ PC
    #identity_functor := ExtendFunctorToFiniteStrictProductCompletionData( PC, coyoneda_embedding[2], coyoneda_embedding[3] );
    
    # C → dummy, C_a ↦ dummy_a
    object_function := function ( obj )
        return dummy_a;
    end;
    
    morphism_function := function ( source_D, mor, range_D )
        return IdentityMorphism( dummy, source_D );
    end;
    
    # PC -> dummy
    universal_functor := ExtendFunctorToFiniteStrictProductCompletionData( PC, Pair( object_function, morphism_function ), dummy );
    
    return universal_functor[2][2](
                   dummy_a, #identity_functor[2][1]( a ),
                   delta,
                   dummy_aa ); #identity_functor[2][1]( aa ) );
    
end;

#Assert( 0, IsCongruentForMorphisms( PC, delta, func( PC, a ) ) );

StartTimer( "CartesianDiagonal" );

#StopCompilationAtCategory( PC );
#StopCompilationAtPrimitivelyInstalledOperationsOfCategory( PC );
#StopCompilationAtCategory( UnderlyingCategory( PC ) );
StopCompilationAtCategory( dummy );

# TODO: the following two logic templates only hold up to congruence

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj" ],
        src_template := "ProjectionInFactorOfDirectProductWithGivenDirectProduct( cat, ListWithIdenticalEntries( 1, obj ), 1, obj )",
        dst_template := "IdentityMorphism( cat, obj )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj", "beta" ],
        src_template := "PreCompose( cat, IdentityMorphism( cat, obj ), beta )",
        dst_template := "beta",
    )
);

compiled_func := CapJitCompiledFunction( func, dummy, [ "category", "object", "object" ], "morphism" );

StopTimer( "CartesianDiagonal" );

DisplayTimer( "CartesianDiagonal" );

Display( compiled_func );
