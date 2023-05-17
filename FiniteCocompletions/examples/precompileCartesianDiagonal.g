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

func :=
  function( PC, a )
    local C, C_a, id_C_a, aa, delta, coyoneda_embedding, identity_functor;
    
    C := UnderlyingCategory( PC );
    
    C_a := ObjectDatum( PC, a )[2][1];
    
    id_C_a := IdentityMorphism( C, C_a );
    
    aa := DirectProduct( PC, [ a, a ] );
    
    delta := MorphismConstructor( PC,
                     a,
                     Pair( [ 0, 0 ], [ id_C_a, id_C_a ] ),
                     aa );
    
    ## C → PC
    coyoneda_embedding := CoYonedaEmbeddingOfUnderlyingCategoryData( PC );
    
    ## PC ⭇ PC
    identity_functor := ExtendFunctorToFiniteStrictProductCompletionData( PC, coyoneda_embedding[2], coyoneda_embedding[3] );
    
    return identity_functor[2][2](
                   a, #identity_functor[2][1]( a ),
                   delta,
                   aa ); #identity_functor[2][1]( aa ) );
    
end;

Assert( 0, IsCongruentForMorphisms( PC, delta, func( PC, a ) ) );

StartTimer( "CartesianDiagonal" );

#StopCompilationAtCategory( PC );
#StopCompilationAtPrimitivelyInstalledOperationsOfCategory( PC );
StopCompilationAtCategory( UnderlyingCategory( PC ) );

compiled_func := CapJitCompiledFunction( func, PC, [ "category", "object" ], "morphism" );

StopTimer( "CartesianDiagonal" );

DisplayTimer( "CartesianDiagonal" );

Display( compiled_func );
