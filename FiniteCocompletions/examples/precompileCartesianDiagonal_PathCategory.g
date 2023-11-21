LoadPackage( "FiniteCocompletions", false );
#! true

LoadPackage( "CompilerForCAP", ">= 2022.09-02", false );
#! true

ReadPackageOnce( "FinSetsForCAP", "gap/CompilerLogic.gi" );
#! true

sFinSets := CategoryOfSkeletalFinSets( : no_precompiled_code := true );

C := PathCategory( FinQuiver( "Q(a)[]" ) : range_of_HomStructure := sFinSets );

PC := FiniteStrictProductCompletion( C : no_precompiled_code := true );

a := PC.a;

aa := DirectProduct( PC, [ a, a ] );

implemented_func := { T, A, AA } -> CartesianDiagonalWithGivenCartesianPower( T, A, 2, AA );

delta_implemented := implemented_func( PC, a, aa );

StartTimer( "CartesianDiagonalWithGivenCartesianSquare" );

StopCompilationAtPrimitivelyInstalledOperationsOfCategory( PC );

compiled_implemented_func := CapJitCompiledFunction( implemented_func, PC, [ "category", "object", "object" ], "morphism" );

StopTimer( "CartesianDiagonalWithGivenCartesianSquare" );

DisplayTimer( "CartesianDiagonalWithGivenCartesianSquare" );

Assert( 0, compiled_implemented_func( PC, a, aa ) = delta_implemented );

Display( compiled_implemented_func );

ContinueCompilationAtPrimitivelyInstalledOperationsOfCategory( PC );

###

hom_a_aa := MorphismsOfExternalHom( PC, a, aa );

Assert( 0, Length( hom_a_aa ) = 1 );

delta := hom_a_aa[1];

Assert( 0, delta = delta_implemented );

delta_reconstructed := CellAsEvaluatableString( delta, [ "PC", "C" ] );

Assert( 0, delta = EvalString( delta_reconstructed ) );

T := DummyCategory( rec( name := "A placeholder cartesian category",
             properties := [ "IsCartesianCategory" ],
             list_of_operations_to_install := CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCartesianCategory ) );;

func := EvalString( ReplacedStringViaRecord( """
  function( T, A, AA )
    local objects, generating_morphisms,
          embedding_on_objects, embedding_on_morphisms, extended_functor;
    
    objects := [ A ];
    generating_morphisms := [  ];
    
    ## Q → T
    embedding_on_objects :=
      function( objQ )
        
        return objects[objQ];
        
    end;
    
    embedding_on_morphisms :=
      function( morQ )
        
        return generating_morphisms[morQ];
        
    end;
    
    ## PC → T
    extended_functor :=
      ExtendFunctorToFiniteStrictProductCompletionData(
              PC,
              ExtendFunctorToFpCategoryData(
                      C,
                      Pair( embedding_on_objects, embedding_on_morphisms ),
                      T )[2],
              T );
    
    return extended_functor[2][2](
                   A, #extended_functor[2][1]( a ),
                   delta_reconstructed,
                   AA ); #extended_functor[2][1]( aa ) );
    
end
""",
  rec( delta_reconstructed := delta_reconstructed ) ) );

Assert( 0, func( PC, a, aa ) = delta );

StartTimer( "CartesianDiagonalWithGivenCartesianSquare" );

StopCompilationAtPrimitivelyInstalledOperationsOfCategory( T );

ReadPackageOnce( "FiniteCocompletions",
        "examples/precompileCartesianDiagonal_CompilerLogic.g" );

compiled_func := CapJitCompiledFunction( func, T, [ "category", "object", "object" ], "morphism" );

StopTimer( "CartesianDiagonalWithGivenCartesianSquare" );

DisplayTimer( "CartesianDiagonalWithGivenCartesianSquare" );

Assert( 0, compiled_func( PC, a, aa ) = delta );

Display( compiled_func );
#! function ( T_1, A_1, AA_1 )
#!     local deduped_1_1;
#!     deduped_1_1 := IdentityMorphism( T_1, A_1 );
#!     return UniversalMorphismIntoDirectProductWithGivenDirectProduct( T_1, ListWithIdenticalEntries( 2, A_1 ), A_1, [ deduped_1_1, deduped_1_1 ], AA_1 );
#! end