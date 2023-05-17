LoadPackage( "FiniteCocompletions" );

CD :=
function ( PC_1, a_1 )
    local hoisted_1_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1,
    deduped_14_1;
    deduped_14_1 := PairOfIntAndList( a_1 );
    deduped_13_1 := deduped_14_1[2];
    deduped_12_1 := deduped_14_1[1];
    deduped_11_1 := deduped_12_1 + deduped_12_1;
    deduped_10_1 := [ 0 .. deduped_11_1 - 1 ];
    deduped_8_1 := List( deduped_13_1, function ( objC_2 )
            return CreateCapCategoryObjectWithAttributes( PC_1, PairOfIntAndList, NTuple( 2, 1, [ objC_2 ] ) );
        end );
    deduped_9_1 := List( [ 0 .. deduped_12_1 - 1 ], function ( i_2 )
            return deduped_8_1[1 + i_2];
        end );
    hoisted_1_1 := Concatenation( deduped_8_1, deduped_8_1 );
    deduped_7_1 := List( deduped_10_1, function ( i_2 )
            return hoisted_1_1[1 + i_2];
        end );
    hoisted_6_1 := ProjectionInFactorOfDirectProductWithGivenDirectProduct( PC_1, deduped_9_1, 1, a_1 );
    hoisted_5_1 := NTuple( 2, [ 0 ], [ IdentityMorphism( UnderlyingCategory( PC_1 ), deduped_13_1[1] ) ] );
    hoisted_4_1 := deduped_9_1[1];
    return UniversalMorphismIntoDirectProductWithGivenDirectProduct( PC_1, deduped_7_1, a_1, List( deduped_10_1, function ( i_2 )
              return PreCompose( PC_1, hoisted_6_1, CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryMorphismWithAttributes( PC_1,
                     deduped_7_1[1 + CAP_JIT_INCOMPLETE_LOGIC( i_2 )], hoisted_4_1, PairOfLists, hoisted_5_1 ) ) );
          end ), CreateCapCategoryObjectWithAttributes( PC_1, PairOfIntAndList, NTuple( 2, deduped_11_1, Concatenation( deduped_13_1, deduped_13_1 ) ) ) );
end;
