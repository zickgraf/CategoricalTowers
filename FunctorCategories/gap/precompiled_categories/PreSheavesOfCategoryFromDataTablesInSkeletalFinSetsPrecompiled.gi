# SPDX-License-Identifier: GPL-2.0-or-later
# FunctorCategories: Categories of functors
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_PreSheavesOfCategoryFromDataTablesInSkeletalFinSetsPrecompiled", function ( cat )
    
    ##
    AddInitialObject( cat,
        
########
function ( cat_1 )
    local hoisted_2_1, deduped_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Target( cat_1 );
    deduped_5_1 := Source( cat_1 );
    deduped_4_1 := CreateCapCategoryObjectWithAttributes( deduped_6_1, Length, BigInt( 0 ) );
    deduped_3_1 := DefiningTripleOfUnderlyingQuiver( deduped_5_1 );
    hoisted_2_1 := CreateCapCategoryMorphismWithAttributes( deduped_6_1, deduped_4_1, deduped_4_1, AsList, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsInt ) );
          end ) );
    return CreateCapCategoryObjectWithAttributes( cat_1, Source, deduped_5_1, Target, deduped_6_1, ValuesOfPreSheaf, NTuple( 2, LazyHList( [ 1 .. deduped_3_1[1] ], function ( o_2 )
                return deduped_4_1;
            end ), LazyHList( [ 1 .. deduped_3_1[2] ], function ( m_2 )
                return hoisted_2_1;
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddCoproduct( cat,
        
########
function ( cat_1, objects_1 )
    local hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Target( cat_1 );
    deduped_5_1 := Source( cat_1 );
    deduped_4_1 := DefiningTripleOfUnderlyingQuiver( deduped_5_1 );
    hoisted_3_1 := [ 1 .. Length( objects_1 ) ];
    hoisted_2_1 := deduped_4_1[3];
    return CreateCapCategoryObjectWithAttributes( cat_1, Source, deduped_5_1, Target, deduped_6_1, ValuesOfPreSheaf, NTuple( 2, LazyHList( [ 1 .. deduped_4_1[1] ], function ( o_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_6_1, Length, Sum( List( objects_1, function ( F_3 )
                            return CAP_JIT_INCOMPLETE_LOGIC( Length( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][o_2] ) ) );
                        end ) ) );
            end ), LazyHList( [ 1 .. deduped_4_1[2] ], function ( m_2 )
                local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                deduped_4_2 := hoisted_2_1[m_2];
                deduped_3_2 := List( objects_1, function ( F_3 )
                        return CAP_JIT_INCOMPLETE_LOGIC( Length( Range( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[2][m_2] ) ) ) );
                    end );
                hoisted_2_2 := 1 + deduped_4_2[1];
                hoisted_1_2 := 1 + deduped_4_2[2];
                return CreateCapCategoryMorphismWithAttributes( deduped_6_1, CreateCapCategoryObjectWithAttributes( deduped_6_1, Length, Sum( List( objects_1, function ( F_3 )
                              return CAP_JIT_INCOMPLETE_LOGIC( Length( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][hoisted_1_2] ) ) );
                          end ) ) ), CreateCapCategoryObjectWithAttributes( deduped_6_1, Length, Sum( List( objects_1, function ( F_3 )
                              return CAP_JIT_INCOMPLETE_LOGIC( Length( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][hoisted_2_2] ) ) );
                          end ) ) ), AsList, Concatenation( List( hoisted_3_1, function ( i_3 )
                            local hoisted_1_3, hoisted_2_3, deduped_3_3, deduped_4_3;
                            deduped_4_3 := Sum( deduped_3_2{[ 1 .. i_3 - 1 ]} );
                            deduped_3_3 := CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( CAP_JIT_INCOMPLETE_LOGIC( objects_1[i_3] ) )[2][m_2] );
                            hoisted_2_3 := [ deduped_4_3 .. deduped_4_3 + deduped_3_2[i_3] - 1 ];
                            hoisted_1_3 := CAP_JIT_INCOMPLETE_LOGIC( AsList( deduped_3_3 ) );
                            return List( [ 0 .. CAP_JIT_INCOMPLETE_LOGIC( Length( Source( deduped_3_3 ) ) ) - 1 ], function ( i_4 )
                                    return hoisted_2_3[1 + hoisted_1_3[(1 + i_4)]];
                                end );
                        end ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddInjectionOfCofactorOfCoproductWithGivenCoproduct( cat,
        
########
function ( cat_1, objects_1, k_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1;
    deduped_5_1 := objects_1[k_1];
    hoisted_4_1 := Target( cat_1 );
    hoisted_3_1 := [ 1 .. k_1 - 1 ];
    hoisted_2_1 := ValuesOfPreSheaf( P_1 )[1];
    hoisted_1_1 := ValuesOfPreSheaf( CAP_JIT_INCOMPLETE_LOGIC( deduped_5_1 ) )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_5_1, P_1, ValuesOnAllObjects, LazyHList( [ 1 .. DefiningTripleOfUnderlyingQuiver( Source( cat_1 ) )[1] ], function ( o_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := List( objects_1, function ( F_3 )
                      return CAP_JIT_INCOMPLETE_LOGIC( Length( CAP_JIT_INCOMPLETE_LOGIC( ValuesOfPreSheaf( F_3 )[1][o_2] ) ) );
                  end );
              deduped_1_2 := Sum( deduped_2_2{hoisted_3_1} );
              return CreateCapCategoryMorphismWithAttributes( hoisted_4_1, CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[o_2] ), hoisted_2_1[o_2], AsList, [ deduped_1_2 .. deduped_1_2 + deduped_2_2[k_1] - 1 ] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismFromCoproductWithGivenCoproduct( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1;
    hoisted_3_1 := Target( cat_1 );
    hoisted_2_1 := ValuesOfPreSheaf( T_1 )[1];
    hoisted_1_1 := ValuesOfPreSheaf( P_1 )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ValuesOnAllObjects, LazyHList( [ 1 .. DefiningTripleOfUnderlyingQuiver( Source( cat_1 ) )[1] ], function ( o_2 )
              return CreateCapCategoryMorphismWithAttributes( hoisted_3_1, hoisted_1_1[o_2], hoisted_2_1[o_2], AsList, Concatenation( List( tau_1, function ( eta_3 )
                          return CAP_JIT_INCOMPLETE_LOGIC( AsList( CAP_JIT_INCOMPLETE_LOGIC( ValuesOnAllObjects( eta_3 )[o_2] ) ) );
                      end ) ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_10_1, deduped_11_1, hoisted_12_1, hoisted_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, hoisted_26_1, deduped_28_1, hoisted_30_1, hoisted_31_1, hoisted_32_1, deduped_33_1, deduped_35_1, deduped_36_1, hoisted_37_1, hoisted_38_1, hoisted_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1, deduped_44_1, deduped_45_1, deduped_46_1, deduped_47_1, deduped_48_1, deduped_49_1, deduped_50_1, deduped_51_1, deduped_52_1, deduped_53_1, deduped_54_1, deduped_55_1, deduped_56_1;
    deduped_56_1 := ValuesOfPreSheaf( arg3_1 );
    deduped_55_1 := ValuesOfPreSheaf( arg2_1 );
    deduped_54_1 := Source( cat_1 );
    deduped_53_1 := deduped_55_1[2];
    deduped_52_1 := DataTables( deduped_54_1 );
    deduped_51_1 := DefiningTripleOfUnderlyingQuiver( deduped_54_1 );
    deduped_50_1 := deduped_52_1[2];
    deduped_49_1 := deduped_52_1[1];
    deduped_48_1 := [ 0 .. deduped_51_1[2] - 1 ];
    deduped_47_1 := [ 0 .. deduped_51_1[1] - 1 ];
    deduped_46_1 := [ 0 .. deduped_49_1[2] - 1 ];
    deduped_1_1 := List( deduped_55_1[1], Length );
    deduped_45_1 := List( deduped_47_1, function ( o_2 )
            return deduped_1_1[1 + o_2];
        end );
    deduped_2_1 := List( deduped_56_1[1], Length );
    deduped_44_1 := Concatenation( List( deduped_47_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
          end ) );
    deduped_43_1 := Product( deduped_44_1 );
    deduped_7_1 := List( [ 0 .. deduped_49_1[1] - 1 ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_54_1, IndexOfObject, i_2 );
        end );
    deduped_3_1 := deduped_51_1[3];
    deduped_6_1 := List( deduped_48_1, function ( m_2 )
            return deduped_3_1[1 + m_2][1];
        end );
    deduped_4_1 := List( deduped_48_1, function ( m_2 )
            return deduped_3_1[1 + m_2][2];
        end );
    deduped_8_1 := List( deduped_48_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_1_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[1 + deduped_6_1[deduped_2_2]] ) );
        end );
    deduped_42_1 := [ 0 .. Sum( List( deduped_48_1, function ( i_2 )
                    return deduped_8_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_41_1 := [ 0 .. deduped_43_1 - 1 ];
    deduped_40_1 := [ 0 .. Sum( List( deduped_48_1, function ( m_2 )
                    return deduped_1_1[1 + deduped_3_1[(1 + m_2)][2]];
                end ) ) - 1 ];
    deduped_20_1 := List( deduped_47_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_1_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[deduped_2_2] ) );
        end );
    deduped_14_1 := deduped_50_1[3];
    deduped_11_1 := deduped_50_1[2];
    deduped_16_1 := List( deduped_46_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_54_1, CreateCapCategoryObjectWithAttributes( deduped_54_1, IndexOfObject, deduped_11_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_54_1, IndexOfObject, deduped_14_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_15_1 := deduped_50_1[1];
    deduped_36_1 := List( deduped_48_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_4_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_45_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_45_1[deduped_2_2] - 1 ], List( deduped_20_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    deduped_24_1 := List( IndicesOfGeneratingMorphisms( deduped_54_1 ), function ( i_2 )
            return deduped_16_1[1 + i_2];
        end );
    deduped_35_1 := List( deduped_48_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_1_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_24_1[deduped_2_2] ) );
        end );
    deduped_28_1 := Sum( deduped_45_1 );
    hoisted_38_1 := Concatenation( List( deduped_48_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_36_1[deduped_3_2][1];
              hoisted_1_2 := deduped_35_1[deduped_3_2][1];
              return List( [ 0 .. deduped_8_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_44_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_44_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_43_1, deduped_4_3, deduped_5_3 * Product( deduped_44_1{[ (deduped_6_3 + 1) .. deduped_28_1 ]} ) );
                      return List( deduped_41_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_43_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    deduped_25_1 := List( deduped_56_1[2], AsList );
    deduped_23_1 := List( deduped_46_1, function ( i_2 )
            return deduped_14_1[1 + i_2];
        end );
    deduped_22_1 := List( deduped_46_1, function ( i_2 )
            return deduped_11_1[1 + i_2];
        end );
    deduped_18_1 := deduped_50_1[4];
    hoisted_37_1 := Concatenation( List( deduped_48_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_35_1[deduped_5_2];
              hoisted_3_2 := List( deduped_36_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_8_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_2_1[deduped_6_3] - 1 ];
                      else
                          return deduped_25_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_10_1 := Concatenation( List( deduped_48_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_8_1[1 + i_2][1], deduped_43_1 );
          end ) );
    hoisted_39_1 := List( deduped_42_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_37_1[deduped_3_2];
            hoisted_1_2 := hoisted_38_1[deduped_3_2];
            return List( [ 0 .. deduped_10_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_32_1 := Concatenation( List( deduped_48_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( deduped_1_1[1 + deduped_4_1[deduped_1_2]], deduped_2_1[1 + deduped_6_1[deduped_1_2]] );
          end ) );
    deduped_33_1 := List( deduped_40_1, function ( j_2 )
            return Product( hoisted_32_1{[ 1 .. j_2 ]} );
        end );
    deduped_21_1 := List( deduped_48_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_6_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_45_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_45_1[deduped_2_2] - 1 ], List( deduped_20_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    hoisted_13_1 := List( deduped_53_1, function ( logic_new_func_x_2 )
            return Length( Source( logic_new_func_x_2 ) );
        end );
    hoisted_12_1 := List( deduped_53_1, AsList );
    deduped_17_1 := List( deduped_48_1, function ( m_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + m_2;
            return NTuple( 2, hoisted_12_1[deduped_1_2], ListWithIdenticalEntries( hoisted_13_1[deduped_1_2], deduped_16_1[1 + deduped_15_1[(1 + deduped_6_1[deduped_1_2])]] ) );
        end );
    hoisted_30_1 := Concatenation( List( deduped_48_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_21_1[deduped_3_2][1];
              hoisted_1_2 := deduped_17_1[deduped_3_2][1];
              return List( [ 0 .. deduped_8_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_44_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_44_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_43_1, deduped_4_3, deduped_5_3 * Product( deduped_44_1{[ (deduped_6_3 + 1) .. deduped_28_1 ]} ) );
                      return List( deduped_41_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_43_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_26_1 := Concatenation( List( deduped_48_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_17_1[deduped_5_2];
              hoisted_3_2 := List( deduped_21_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_8_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_2_1[deduped_6_3] - 1 ];
                      else
                          return deduped_25_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_31_1 := List( deduped_42_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_26_1[deduped_3_2];
            hoisted_1_2 := hoisted_30_1[deduped_3_2];
            return List( [ 0 .. deduped_10_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    return CreateCapCategoryObjectWithAttributes( Target( cat_1 ), Length, Length( Filtered( deduped_41_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
                return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_40_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_31_1[deduped_1_3][deduped_1_2] * deduped_33_1[deduped_1_3];
                        end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_40_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_39_1[deduped_1_3][deduped_1_2] * deduped_33_1[deduped_1_3];
                        end ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, beta_1, range_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_10_1, deduped_11_1, hoisted_12_1, hoisted_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, hoisted_26_1, hoisted_30_1, hoisted_31_1, hoisted_32_1, deduped_33_1, deduped_35_1, deduped_36_1, hoisted_37_1, hoisted_38_1, hoisted_39_1, deduped_40_1, deduped_41_1, hoisted_42_1, hoisted_43_1, hoisted_47_1, hoisted_48_1, hoisted_51_1, hoisted_52_1, hoisted_53_1, deduped_54_1, deduped_55_1, deduped_56_1, hoisted_57_1, deduped_60_1, hoisted_62_1, hoisted_63_1, hoisted_64_1, hoisted_65_1, deduped_66_1, deduped_67_1, hoisted_68_1, hoisted_69_1, deduped_70_1, deduped_71_1, hoisted_72_1, hoisted_73_1, hoisted_74_1, hoisted_75_1, deduped_76_1, deduped_78_1, deduped_79_1, hoisted_80_1, hoisted_81_1, hoisted_82_1, hoisted_83_1, hoisted_84_1, hoisted_85_1, deduped_86_1, deduped_87_1, deduped_88_1, deduped_89_1, deduped_90_1, deduped_91_1, deduped_92_1, deduped_93_1, deduped_94_1, deduped_95_1, deduped_96_1, deduped_97_1, deduped_98_1, deduped_99_1, deduped_100_1, deduped_101_1, deduped_102_1, deduped_103_1, deduped_104_1, deduped_105_1, deduped_106_1, deduped_107_1, deduped_108_1, deduped_109_1, deduped_110_1, deduped_111_1, deduped_112_1, deduped_113_1, deduped_114_1, deduped_115_1, deduped_116_1, deduped_117_1, deduped_118_1, deduped_119_1;
    deduped_119_1 := Source( cat_1 );
    deduped_118_1 := ListOfValues( ValuesOnAllObjects( alpha_1 ) );
    deduped_117_1 := ValuesOfPreSheaf( Source( beta_1 ) );
    deduped_116_1 := ValuesOfPreSheaf( Target( alpha_1 ) );
    deduped_115_1 := DataTables( deduped_119_1 );
    deduped_114_1 := DefiningTripleOfUnderlyingQuiver( deduped_119_1 );
    deduped_113_1 := ValuesOfPreSheaf( Target( beta_1 ) );
    deduped_112_1 := ValuesOfPreSheaf( Source( alpha_1 ) );
    deduped_111_1 := deduped_116_1[2];
    deduped_110_1 := deduped_112_1[2];
    deduped_109_1 := deduped_115_1[2];
    deduped_108_1 := deduped_114_1[1];
    deduped_107_1 := deduped_115_1[1];
    deduped_106_1 := [ 1 .. deduped_108_1 ];
    deduped_105_1 := [ 0 .. deduped_108_1 - 1 ];
    deduped_104_1 := [ 0 .. deduped_114_1[2] - 1 ];
    deduped_103_1 := [ 0 .. deduped_107_1[2] - 1 ];
    deduped_40_1 := List( deduped_116_1[1], Length );
    deduped_102_1 := List( deduped_105_1, function ( o_2 )
            return deduped_40_1[1 + o_2];
        end );
    deduped_1_1 := List( deduped_112_1[1], Length );
    deduped_101_1 := List( deduped_105_1, function ( o_2 )
            return deduped_1_1[1 + o_2];
        end );
    deduped_41_1 := List( deduped_117_1[1], Length );
    deduped_100_1 := Concatenation( List( deduped_105_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_40_1[deduped_1_2], deduped_41_1[deduped_1_2] );
          end ) );
    deduped_99_1 := Concatenation( List( deduped_105_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_41_1[deduped_1_2] );
          end ) );
    deduped_98_1 := Sum( deduped_101_1 );
    deduped_2_1 := List( deduped_113_1[1], Length );
    deduped_97_1 := Concatenation( List( deduped_105_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
          end ) );
    deduped_96_1 := Product( deduped_100_1 );
    deduped_95_1 := Product( deduped_99_1 );
    deduped_94_1 := Product( deduped_97_1 );
    deduped_7_1 := List( [ 0 .. deduped_107_1[1] - 1 ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_119_1, IndexOfObject, i_2 );
        end );
    deduped_3_1 := deduped_114_1[3];
    deduped_6_1 := List( deduped_104_1, function ( m_2 )
            return deduped_3_1[1 + m_2][1];
        end );
    deduped_4_1 := List( deduped_104_1, function ( m_2 )
            return deduped_3_1[1 + m_2][2];
        end );
    deduped_66_1 := List( deduped_104_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_40_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[1 + deduped_6_1[deduped_2_2]] ) );
        end );
    deduped_93_1 := [ 0 .. Sum( List( deduped_104_1, function ( i_2 )
                    return deduped_66_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_92_1 := [ 0 .. deduped_98_1 - 1 ];
    deduped_8_1 := List( deduped_104_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_1_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[1 + deduped_6_1[deduped_2_2]] ) );
        end );
    deduped_91_1 := [ 0 .. Sum( List( deduped_104_1, function ( i_2 )
                    return deduped_8_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_90_1 := [ 0 .. deduped_96_1 - 1 ];
    deduped_89_1 := [ 0 .. deduped_95_1 - 1 ];
    deduped_88_1 := [ 0 .. deduped_94_1 - 1 ];
    deduped_87_1 := [ 0 .. Sum( List( deduped_104_1, function ( m_2 )
                    return deduped_40_1[1 + deduped_3_1[(1 + m_2)][2]];
                end ) ) - 1 ];
    deduped_86_1 := [ 0 .. Sum( List( deduped_104_1, function ( m_2 )
                    return deduped_1_1[1 + deduped_3_1[(1 + m_2)][2]];
                end ) ) - 1 ];
    deduped_20_1 := List( deduped_105_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_1_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[deduped_2_2] ) );
        end );
    deduped_14_1 := deduped_109_1[3];
    deduped_11_1 := deduped_109_1[2];
    deduped_16_1 := List( deduped_103_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_119_1, CreateCapCategoryObjectWithAttributes( deduped_119_1, IndexOfObject, deduped_11_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_119_1, IndexOfObject, deduped_14_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_15_1 := deduped_109_1[1];
    deduped_36_1 := List( deduped_104_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_4_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_101_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_101_1[deduped_2_2] - 1 ], List( deduped_20_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    deduped_24_1 := List( IndicesOfGeneratingMorphisms( deduped_119_1 ), function ( i_2 )
            return deduped_16_1[1 + i_2];
        end );
    deduped_35_1 := List( deduped_104_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_1_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_24_1[deduped_2_2] ) );
        end );
    hoisted_38_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_36_1[deduped_3_2][1];
              hoisted_1_2 := deduped_35_1[deduped_3_2][1];
              return List( [ 0 .. deduped_8_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_97_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_97_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_94_1, deduped_4_3, deduped_5_3 * Product( deduped_97_1{[ (deduped_6_3 + 1) .. deduped_98_1 ]} ) );
                      return List( deduped_88_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_94_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    deduped_25_1 := List( deduped_113_1[2], AsList );
    deduped_23_1 := List( deduped_103_1, function ( i_2 )
            return deduped_14_1[1 + i_2];
        end );
    deduped_22_1 := List( deduped_103_1, function ( i_2 )
            return deduped_11_1[1 + i_2];
        end );
    deduped_18_1 := deduped_109_1[4];
    hoisted_37_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_35_1[deduped_5_2];
              hoisted_3_2 := List( deduped_36_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_8_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_2_1[deduped_6_3] - 1 ];
                      else
                          return deduped_25_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_10_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_8_1[1 + i_2][1], deduped_94_1 );
          end ) );
    hoisted_39_1 := List( deduped_91_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_37_1[deduped_3_2];
            hoisted_1_2 := hoisted_38_1[deduped_3_2];
            return List( [ 0 .. deduped_10_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_32_1 := Concatenation( List( deduped_104_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( deduped_1_1[1 + deduped_4_1[deduped_1_2]], deduped_2_1[1 + deduped_6_1[deduped_1_2]] );
          end ) );
    deduped_33_1 := List( deduped_86_1, function ( j_2 )
            return Product( hoisted_32_1{[ 1 .. j_2 ]} );
        end );
    deduped_21_1 := List( deduped_104_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_6_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_101_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_101_1[deduped_2_2] - 1 ], List( deduped_20_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    hoisted_13_1 := List( deduped_110_1, function ( logic_new_func_x_2 )
            return Length( Source( logic_new_func_x_2 ) );
        end );
    hoisted_12_1 := List( deduped_110_1, AsList );
    deduped_17_1 := List( deduped_104_1, function ( m_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + m_2;
            return NTuple( 2, hoisted_12_1[deduped_1_2], ListWithIdenticalEntries( hoisted_13_1[deduped_1_2], deduped_16_1[1 + deduped_15_1[(1 + deduped_6_1[deduped_1_2])]] ) );
        end );
    hoisted_30_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_21_1[deduped_3_2][1];
              hoisted_1_2 := deduped_17_1[deduped_3_2][1];
              return List( [ 0 .. deduped_8_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_97_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_97_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_94_1, deduped_4_3, deduped_5_3 * Product( deduped_97_1{[ (deduped_6_3 + 1) .. deduped_98_1 ]} ) );
                      return List( deduped_88_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_94_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_26_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_17_1[deduped_5_2];
              hoisted_3_2 := List( deduped_21_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_8_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_2_1[deduped_6_3] - 1 ];
                      else
                          return deduped_25_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_31_1 := List( deduped_91_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_26_1[deduped_3_2];
            hoisted_1_2 := hoisted_30_1[deduped_3_2];
            return List( [ 0 .. deduped_10_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_85_1 := Filtered( deduped_88_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_86_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_31_1[deduped_1_3][deduped_1_2] * deduped_33_1[deduped_1_3];
                    end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_86_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_39_1[deduped_1_3][deduped_1_2] * deduped_33_1[deduped_1_3];
                    end ) );
        end );
    hoisted_48_1 := List( deduped_92_1, function ( j_2 )
            return Product( deduped_97_1{[ 1 .. j_2 ]} );
        end );
    hoisted_42_1 := List( ValuesOnAllObjects( beta_1 ), AsList );
    hoisted_43_1 := Concatenation( List( deduped_105_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], hoisted_42_1[deduped_1_2] );
          end ) );
    hoisted_47_1 := List( [ 1 .. deduped_98_1 ], function ( i_2 )
            local hoisted_3_2, hoisted_4_2, deduped_5_2, deduped_6_2;
            deduped_6_2 := deduped_99_1[i_2];
            deduped_5_2 := Product( deduped_99_1{[ 1 .. i_2 - 1 ]} );
            hoisted_4_2 := hoisted_43_1[i_2];
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_95_1, deduped_5_2, deduped_6_2 * Product( deduped_99_1{[ (i_2 + 1) .. deduped_98_1 ]} ) );
            return List( deduped_89_1, function ( i_3 )
                    return hoisted_4_2[1 + RemIntWithDomain( QuoIntWithDomain( i_3, deduped_5_2, deduped_95_1 ), deduped_6_2, hoisted_3_2 )];
                end );
        end );
    hoisted_65_1 := List( deduped_89_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return Sum( deduped_92_1, function ( j_3 )
                    local deduped_1_3;
                    deduped_1_3 := 1 + j_3;
                    return hoisted_47_1[deduped_1_3][hoisted_1_2] * hoisted_48_1[deduped_1_3];
                end );
        end );
    hoisted_64_1 := List( deduped_92_1, function ( j_2 )
            return Product( deduped_99_1{[ 1 .. j_2 ]} );
        end );
    deduped_60_1 := Sum( deduped_102_1 );
    hoisted_53_1 := List( deduped_118_1, function ( logic_new_func_x_2 )
            return Length( Source( logic_new_func_x_2 ) );
        end );
    hoisted_52_1 := List( deduped_118_1, AsList );
    deduped_54_1 := List( deduped_105_1, function ( o_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + o_2;
            return NTuple( 2, hoisted_52_1[deduped_1_2], ListWithIdenticalEntries( hoisted_53_1[deduped_1_2], deduped_16_1[1 + deduped_15_1[deduped_1_2]] ) );
        end );
    hoisted_62_1 := Concatenation( List( deduped_106_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := Sum( deduped_102_1{[ 1 .. i_2 - 1 ]} );
              hoisted_2_2 := [ deduped_3_2 .. deduped_3_2 + deduped_102_1[i_2] - 1 ];
              hoisted_1_2 := deduped_54_1[i_2][1];
              return List( [ 0 .. deduped_20_1[i_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_100_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_100_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_96_1, deduped_4_3, deduped_5_3 * Product( deduped_100_1{[ (deduped_6_3 + 1) .. deduped_60_1 ]} ) );
                      return List( deduped_90_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_96_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    deduped_56_1 := List( deduped_117_1[2], AsList );
    deduped_55_1 := List( deduped_105_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_40_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[deduped_2_2] ) );
        end );
    hoisted_57_1 := Concatenation( List( deduped_106_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2;
              deduped_4_2 := deduped_54_1[i_2];
              hoisted_3_2 := List( deduped_55_1[i_2][2], function ( objC_3 )
                      return deduped_15_1[1 + IndexOfObject( objC_3 )];
                  end );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_20_1[i_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_41_1[deduped_6_3] - 1 ];
                      else
                          return deduped_56_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_51_1 := Concatenation( List( deduped_106_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_20_1[i_2][1], deduped_96_1 );
          end ) );
    hoisted_63_1 := List( [ 0 .. Sum( List( deduped_106_1, function ( i_2 )
                      return deduped_20_1[i_2][1];
                  end ) ) - 1 ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_57_1[deduped_3_2];
            hoisted_1_2 := hoisted_62_1[deduped_3_2];
            return List( [ 0 .. hoisted_51_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_84_1 := List( deduped_90_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + i_2;
            return hoisted_65_1[1 + Sum( deduped_92_1, function ( j_3 )
                       local deduped_1_3;
                       deduped_1_3 := (1 + j_3);
                       return hoisted_63_1[deduped_1_3][hoisted_1_2] * hoisted_64_1[deduped_1_3];
                   end )];
        end );
    deduped_79_1 := List( deduped_104_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_4_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_102_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_102_1[deduped_2_2] - 1 ], List( deduped_55_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    deduped_78_1 := List( deduped_104_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_40_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_24_1[deduped_2_2] ) );
        end );
    hoisted_81_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_79_1[deduped_3_2][1];
              hoisted_1_2 := deduped_78_1[deduped_3_2][1];
              return List( [ 0 .. deduped_66_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_100_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_100_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_96_1, deduped_4_3, deduped_5_3 * Product( deduped_100_1{[ (deduped_6_3 + 1) .. deduped_60_1 ]} ) );
                      return List( deduped_90_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_96_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_80_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_78_1[deduped_5_2];
              hoisted_3_2 := List( deduped_79_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_66_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_41_1[deduped_6_3] - 1 ];
                      else
                          return deduped_56_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_67_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_66_1[1 + i_2][1], deduped_96_1 );
          end ) );
    hoisted_82_1 := List( deduped_93_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_80_1[deduped_3_2];
            hoisted_1_2 := hoisted_81_1[deduped_3_2];
            return List( [ 0 .. deduped_67_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_75_1 := Concatenation( List( deduped_104_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( deduped_40_1[1 + deduped_4_1[deduped_1_2]], deduped_41_1[1 + deduped_6_1[deduped_1_2]] );
          end ) );
    deduped_76_1 := List( deduped_87_1, function ( j_2 )
            return Product( hoisted_75_1{[ 1 .. j_2 ]} );
        end );
    deduped_71_1 := List( deduped_104_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_6_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_102_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_102_1[deduped_2_2] - 1 ], List( deduped_55_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    hoisted_69_1 := List( deduped_111_1, function ( logic_new_func_x_2 )
            return Length( Source( logic_new_func_x_2 ) );
        end );
    hoisted_68_1 := List( deduped_111_1, AsList );
    deduped_70_1 := List( deduped_104_1, function ( m_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + m_2;
            return NTuple( 2, hoisted_68_1[deduped_1_2], ListWithIdenticalEntries( hoisted_69_1[deduped_1_2], deduped_16_1[1 + deduped_15_1[(1 + deduped_6_1[deduped_1_2])]] ) );
        end );
    hoisted_73_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_71_1[deduped_3_2][1];
              hoisted_1_2 := deduped_70_1[deduped_3_2][1];
              return List( [ 0 .. deduped_66_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_100_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_100_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_96_1, deduped_4_3, deduped_5_3 * Product( deduped_100_1{[ (deduped_6_3 + 1) .. deduped_60_1 ]} ) );
                      return List( deduped_90_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_96_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_72_1 := Concatenation( List( deduped_104_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_70_1[deduped_5_2];
              hoisted_3_2 := List( deduped_71_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_66_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_41_1[deduped_6_3] - 1 ];
                      else
                          return deduped_56_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_74_1 := List( deduped_93_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_72_1[deduped_3_2];
            hoisted_1_2 := hoisted_73_1[deduped_3_2];
            return List( [ 0 .. deduped_67_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_83_1 := Filtered( deduped_90_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_87_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_74_1[deduped_1_3][deduped_1_2] * deduped_76_1[deduped_1_3];
                    end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_87_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_82_1[deduped_1_3][deduped_1_2] * deduped_76_1[deduped_1_3];
                    end ) );
        end );
    return CreateCapCategoryMorphismWithAttributes( Target( cat_1 ), source_1, range_1, AsList, List( [ 0 .. Length( source_1 ) - 1 ], function ( x_2 )
              return -1 + BigInt( SafePosition( hoisted_85_1, CAP_JIT_INCOMPLETE_LOGIC( hoisted_84_1[(1 + hoisted_83_1[(1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 ))])] ) ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local deduped_3_1, deduped_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_13_1, deduped_14_1, hoisted_15_1, hoisted_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, hoisted_29_1, deduped_31_1, hoisted_33_1, hoisted_34_1, hoisted_35_1, deduped_36_1, deduped_38_1, deduped_39_1, hoisted_40_1, hoisted_41_1, hoisted_42_1, deduped_43_1, hoisted_44_1, hoisted_46_1, deduped_47_1, deduped_48_1, deduped_49_1, deduped_50_1, deduped_51_1, deduped_52_1, deduped_53_1, deduped_54_1, deduped_55_1, deduped_56_1, deduped_57_1, deduped_58_1, deduped_59_1, deduped_60_1, deduped_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1;
    deduped_68_1 := ValuesOfPreSheaf( range_1 );
    deduped_67_1 := ValuesOfPreSheaf( source_1 );
    deduped_66_1 := Source( cat_1 );
    deduped_65_1 := deduped_67_1[2];
    deduped_64_1 := DataTables( deduped_66_1 );
    deduped_63_1 := deduped_68_1[1];
    deduped_62_1 := deduped_67_1[1];
    deduped_61_1 := DefiningTripleOfUnderlyingQuiver( deduped_66_1 );
    deduped_60_1 := deduped_64_1[2];
    deduped_59_1 := deduped_64_1[1];
    deduped_58_1 := ListOfValues( deduped_62_1 );
    deduped_57_1 := deduped_61_1[1];
    deduped_56_1 := [ 1 .. deduped_57_1 ];
    deduped_55_1 := [ 0 .. deduped_57_1 - 1 ];
    deduped_54_1 := [ 0 .. deduped_61_1[2] - 1 ];
    deduped_53_1 := [ 0 .. deduped_59_1[2] - 1 ];
    deduped_4_1 := List( deduped_62_1, Length );
    deduped_52_1 := List( deduped_55_1, function ( o_2 )
            return deduped_4_1[1 + o_2];
        end );
    deduped_5_1 := List( deduped_63_1, Length );
    deduped_51_1 := Concatenation( List( deduped_55_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_4_1[deduped_1_2], deduped_5_1[deduped_1_2] );
          end ) );
    deduped_50_1 := Product( deduped_51_1 );
    deduped_10_1 := List( [ 0 .. deduped_59_1[1] - 1 ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_66_1, IndexOfObject, i_2 );
        end );
    deduped_6_1 := deduped_61_1[3];
    deduped_9_1 := List( deduped_54_1, function ( m_2 )
            return deduped_6_1[1 + m_2][1];
        end );
    deduped_7_1 := List( deduped_54_1, function ( m_2 )
            return deduped_6_1[1 + m_2][2];
        end );
    deduped_11_1 := List( deduped_54_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_4_1[1 + deduped_7_1[deduped_2_2]];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_10_1[1 + deduped_9_1[deduped_2_2]] ) );
        end );
    deduped_49_1 := [ 0 .. Sum( List( deduped_54_1, function ( i_2 )
                    return deduped_11_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_48_1 := [ 0 .. deduped_50_1 - 1 ];
    deduped_47_1 := [ 0 .. Sum( List( deduped_54_1, function ( m_2 )
                    return deduped_4_1[1 + deduped_6_1[(1 + m_2)][2]];
                end ) ) - 1 ];
    hoisted_46_1 := Target( cat_1 );
    deduped_23_1 := List( deduped_55_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_4_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_10_1[deduped_2_2] ) );
        end );
    deduped_17_1 := deduped_60_1[3];
    deduped_14_1 := deduped_60_1[2];
    deduped_19_1 := List( deduped_53_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_66_1, CreateCapCategoryObjectWithAttributes( deduped_66_1, IndexOfObject, deduped_14_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_66_1, IndexOfObject, deduped_17_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_18_1 := deduped_60_1[1];
    deduped_39_1 := List( deduped_54_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_7_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_52_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_52_1[deduped_2_2] - 1 ], List( deduped_23_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_19_1[1 + deduped_18_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    deduped_27_1 := List( IndicesOfGeneratingMorphisms( deduped_66_1 ), function ( i_2 )
            return deduped_19_1[1 + i_2];
        end );
    deduped_38_1 := List( deduped_54_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_4_1[1 + deduped_7_1[deduped_2_2]];
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_27_1[deduped_2_2] ) );
        end );
    deduped_31_1 := Sum( deduped_52_1 );
    hoisted_41_1 := Concatenation( List( deduped_54_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_39_1[deduped_3_2][1];
              hoisted_1_2 := deduped_38_1[deduped_3_2][1];
              return List( [ 0 .. deduped_11_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_51_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_51_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_50_1, deduped_4_3, deduped_5_3 * Product( deduped_51_1{[ (deduped_6_3 + 1) .. deduped_31_1 ]} ) );
                      return List( deduped_48_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_50_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    deduped_28_1 := List( deduped_68_1[2], AsList );
    deduped_26_1 := List( deduped_53_1, function ( i_2 )
            return deduped_17_1[1 + i_2];
        end );
    deduped_25_1 := List( deduped_53_1, function ( i_2 )
            return deduped_14_1[1 + i_2];
        end );
    deduped_21_1 := deduped_60_1[4];
    hoisted_40_1 := Concatenation( List( deduped_54_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_38_1[deduped_5_2];
              hoisted_3_2 := List( deduped_39_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_11_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_21_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_26_1[deduped_9_3];
                      deduped_7_3 := deduped_25_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_18_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_25_1[deduped_4_3] and deduped_8_3 = deduped_26_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_5_1[deduped_6_3] - 1 ];
                      else
                          return deduped_28_1[SafeUniquePositionProperty( deduped_27_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_13_1 := Concatenation( List( deduped_54_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_11_1[1 + i_2][1], deduped_50_1 );
          end ) );
    hoisted_42_1 := List( deduped_49_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_40_1[deduped_3_2];
            hoisted_1_2 := hoisted_41_1[deduped_3_2];
            return List( [ 0 .. deduped_13_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_35_1 := Concatenation( List( deduped_54_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( deduped_4_1[1 + deduped_7_1[deduped_1_2]], deduped_5_1[1 + deduped_9_1[deduped_1_2]] );
          end ) );
    deduped_36_1 := List( deduped_47_1, function ( j_2 )
            return Product( hoisted_35_1{[ 1 .. j_2 ]} );
        end );
    deduped_24_1 := List( deduped_54_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_9_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_52_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_52_1[deduped_2_2] - 1 ], List( deduped_23_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_19_1[1 + deduped_18_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    hoisted_16_1 := List( deduped_65_1, function ( logic_new_func_x_2 )
            return Length( Source( logic_new_func_x_2 ) );
        end );
    hoisted_15_1 := List( deduped_65_1, AsList );
    deduped_20_1 := List( deduped_54_1, function ( m_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + m_2;
            return NTuple( 2, hoisted_15_1[deduped_1_2], ListWithIdenticalEntries( hoisted_16_1[deduped_1_2], deduped_19_1[1 + deduped_18_1[(1 + deduped_9_1[deduped_1_2])]] ) );
        end );
    hoisted_33_1 := Concatenation( List( deduped_54_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_24_1[deduped_3_2][1];
              hoisted_1_2 := deduped_20_1[deduped_3_2][1];
              return List( [ 0 .. deduped_11_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_51_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_51_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_50_1, deduped_4_3, deduped_5_3 * Product( deduped_51_1{[ (deduped_6_3 + 1) .. deduped_31_1 ]} ) );
                      return List( deduped_48_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_50_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_29_1 := Concatenation( List( deduped_54_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_20_1[deduped_5_2];
              hoisted_3_2 := List( deduped_24_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_11_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_21_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_26_1[deduped_9_3];
                      deduped_7_3 := deduped_25_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_18_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_25_1[deduped_4_3] and deduped_8_3 = deduped_26_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_5_1[deduped_6_3] - 1 ];
                      else
                          return deduped_28_1[SafeUniquePositionProperty( deduped_27_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_34_1 := List( deduped_49_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_29_1[deduped_3_2];
            hoisted_1_2 := hoisted_33_1[deduped_3_2];
            return List( [ 0 .. deduped_13_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_44_1 := CAP_JIT_INCOMPLETE_LOGIC( Filtered( deduped_48_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
                return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_47_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_34_1[deduped_1_3][deduped_1_2] * deduped_36_1[deduped_1_3];
                        end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_47_1, function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := 1 + j_3;
                            return hoisted_42_1[deduped_1_3][deduped_1_2] * deduped_36_1[deduped_1_3];
                        end ) );
            end )[1 + AsList( alpha_1 )[(1 + CAP_JIT_INCOMPLETE_LOGIC( [ 0 .. (Length( Source( alpha_1 ) ) - 1) ][1] ))]] );
    deduped_3_1 := List( deduped_58_1, Length );
    deduped_43_1 := List( deduped_56_1, function ( i_2 )
            return Product( deduped_51_1{[ 1 + Sum( deduped_3_1{[ 1 .. (i_2 - 1) ]} ) .. Sum( deduped_3_1{[ 1 .. i_2 ]} ) ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, ValuesOnAllObjects, List( deduped_56_1, function ( i_2 )
              local hoisted_1_2, hoisted_3_2, deduped_4_2, deduped_5_2, deduped_6_2, deduped_7_2;
              deduped_7_2 := CAP_JIT_INCOMPLETE_LOGIC( i_2 );
              deduped_6_2 := deduped_3_1[i_2];
              deduped_5_2 := deduped_43_1[deduped_7_2];
              deduped_4_2 := Product( deduped_43_1{[ 1 .. deduped_7_2 - 1 ]} );
              hoisted_3_2 := deduped_5_1[i_2];
              hoisted_1_2 := CAP_JIT_INCOMPLETE_LOGIC( RemIntWithDomain( QuoIntWithDomain( hoisted_44_1, deduped_4_2, deduped_50_1 ), deduped_5_2, DivIntWithGivenQuotient( deduped_50_1, deduped_4_2, deduped_5_2 * Product( deduped_43_1{[ (deduped_7_2 + 1) .. deduped_57_1 ]} ) ) ) );
              return CreateCapCategoryMorphismWithAttributes( hoisted_46_1, deduped_58_1[i_2], deduped_63_1[i_2], AsList, List( [ 0 .. deduped_6_2 - 1 ], function ( i_3 )
                        return DigitInPositionalNotation( hoisted_1_2, i_3, deduped_6_2, hoisted_3_2 );
                    end ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddMorphismsOfExternalHom( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_10_1, deduped_11_1, hoisted_12_1, hoisted_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, hoisted_26_1, deduped_28_1, hoisted_30_1, hoisted_31_1, hoisted_32_1, deduped_33_1, deduped_35_1, deduped_36_1, hoisted_37_1, hoisted_38_1, hoisted_39_1, deduped_42_1, deduped_43_1, hoisted_45_1, hoisted_47_1, deduped_49_1, deduped_50_1, deduped_51_1, deduped_52_1, deduped_53_1, deduped_54_1, deduped_55_1, deduped_56_1, deduped_57_1, deduped_58_1, deduped_59_1, deduped_60_1, deduped_61_1, deduped_62_1, deduped_63_1, deduped_64_1, deduped_65_1, deduped_66_1, deduped_67_1, deduped_68_1, deduped_69_1, deduped_70_1, deduped_71_1;
    deduped_71_1 := ValuesOfPreSheaf( arg3_1 );
    deduped_70_1 := ValuesOfPreSheaf( arg2_1 );
    deduped_69_1 := Source( cat_1 );
    deduped_68_1 := deduped_70_1[2];
    deduped_67_1 := DataTables( deduped_69_1 );
    deduped_66_1 := deduped_71_1[1];
    deduped_65_1 := deduped_70_1[1];
    deduped_64_1 := DefiningTripleOfUnderlyingQuiver( deduped_69_1 );
    deduped_63_1 := ListOfValues( deduped_65_1 );
    deduped_62_1 := deduped_67_1[2];
    deduped_61_1 := deduped_67_1[1];
    deduped_60_1 := deduped_64_1[1];
    deduped_59_1 := [ 1 .. deduped_60_1 ];
    deduped_58_1 := [ 0 .. deduped_64_1[2] - 1 ];
    deduped_57_1 := [ 0 .. deduped_60_1 - 1 ];
    deduped_56_1 := [ 0 .. deduped_61_1[2] - 1 ];
    deduped_1_1 := List( deduped_65_1, Length );
    deduped_55_1 := List( deduped_57_1, function ( o_2 )
            return deduped_1_1[1 + o_2];
        end );
    deduped_2_1 := List( deduped_66_1, Length );
    deduped_54_1 := Concatenation( List( deduped_57_1, function ( o_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + o_2;
              return ListWithIdenticalEntries( deduped_1_1[deduped_1_2], deduped_2_1[deduped_1_2] );
          end ) );
    deduped_53_1 := Product( deduped_54_1 );
    deduped_7_1 := List( [ 0 .. deduped_61_1[1] - 1 ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_69_1, IndexOfObject, i_2 );
        end );
    deduped_3_1 := deduped_64_1[3];
    deduped_6_1 := List( deduped_58_1, function ( m_2 )
            return deduped_3_1[1 + m_2][1];
        end );
    deduped_4_1 := List( deduped_58_1, function ( m_2 )
            return deduped_3_1[1 + m_2][2];
        end );
    deduped_8_1 := List( deduped_58_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_1_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[1 + deduped_6_1[deduped_2_2]] ) );
        end );
    deduped_52_1 := [ 0 .. Sum( List( deduped_58_1, function ( i_2 )
                    return deduped_8_1[1 + i_2][1];
                end ) ) - 1 ];
    deduped_51_1 := [ 0 .. deduped_53_1 - 1 ];
    deduped_50_1 := [ 0 .. Sum( List( deduped_58_1, function ( m_2 )
                    return deduped_1_1[1 + deduped_3_1[(1 + m_2)][2]];
                end ) ) - 1 ];
    deduped_20_1 := List( deduped_57_1, function ( o_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + o_2;
            deduped_1_2 := deduped_1_1[deduped_2_2];
            return NTuple( 2, deduped_1_2, ListWithIdenticalEntries( deduped_1_2, deduped_7_1[deduped_2_2] ) );
        end );
    deduped_14_1 := deduped_62_1[3];
    deduped_11_1 := deduped_62_1[2];
    deduped_16_1 := List( deduped_56_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + i_2;
            return CreateCapCategoryMorphismWithAttributes( deduped_69_1, CreateCapCategoryObjectWithAttributes( deduped_69_1, IndexOfObject, deduped_11_1[deduped_1_2] ), CreateCapCategoryObjectWithAttributes( deduped_69_1, IndexOfObject, deduped_14_1[deduped_1_2] ), IndexOfMorphism, i_2 );
        end );
    deduped_15_1 := deduped_62_1[1];
    deduped_36_1 := List( deduped_58_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_4_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_55_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_55_1[deduped_2_2] - 1 ], List( deduped_20_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    deduped_24_1 := List( IndicesOfGeneratingMorphisms( deduped_69_1 ), function ( i_2 )
            return deduped_16_1[1 + i_2];
        end );
    deduped_35_1 := List( deduped_58_1, function ( m_2 )
            local deduped_1_2, deduped_2_2;
            deduped_2_2 := 1 + m_2;
            deduped_1_2 := deduped_1_1[1 + deduped_4_1[deduped_2_2]];
            return NTuple( 2, [ 0 .. deduped_1_2 - 1 ], ListWithIdenticalEntries( deduped_1_2, deduped_24_1[deduped_2_2] ) );
        end );
    deduped_28_1 := Sum( deduped_55_1 );
    hoisted_38_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_36_1[deduped_3_2][1];
              hoisted_1_2 := deduped_35_1[deduped_3_2][1];
              return List( [ 0 .. deduped_8_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_54_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_54_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_53_1, deduped_4_3, deduped_5_3 * Product( deduped_54_1{[ (deduped_6_3 + 1) .. deduped_28_1 ]} ) );
                      return List( deduped_51_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_53_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    deduped_25_1 := List( deduped_71_1[2], AsList );
    deduped_23_1 := List( deduped_56_1, function ( i_2 )
            return deduped_14_1[1 + i_2];
        end );
    deduped_22_1 := List( deduped_56_1, function ( i_2 )
            return deduped_11_1[1 + i_2];
        end );
    deduped_18_1 := deduped_62_1[4];
    hoisted_37_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_35_1[deduped_5_2];
              hoisted_3_2 := List( deduped_36_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_8_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_2_1[deduped_6_3] - 1 ];
                      else
                          return deduped_25_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    deduped_10_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_8_1[1 + i_2][1], deduped_53_1 );
          end ) );
    hoisted_39_1 := List( deduped_52_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_37_1[deduped_3_2];
            hoisted_1_2 := hoisted_38_1[deduped_3_2];
            return List( [ 0 .. deduped_10_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    hoisted_32_1 := Concatenation( List( deduped_58_1, function ( m_2 )
              local deduped_1_2;
              deduped_1_2 := 1 + m_2;
              return ListWithIdenticalEntries( deduped_1_1[1 + deduped_4_1[deduped_1_2]], deduped_2_1[1 + deduped_6_1[deduped_1_2]] );
          end ) );
    deduped_33_1 := List( deduped_50_1, function ( j_2 )
            return Product( hoisted_32_1{[ 1 .. j_2 ]} );
        end );
    deduped_21_1 := List( deduped_58_1, function ( i_2 )
            local deduped_1_2, deduped_2_2, deduped_3_2;
            deduped_3_2 := deduped_6_1[1 + i_2];
            deduped_2_2 := 1 + deduped_3_2;
            deduped_1_2 := Sum( deduped_55_1{[ 1 .. deduped_3_2 ]} );
            return NTuple( 2, [ deduped_1_2 .. deduped_1_2 + deduped_55_1[deduped_2_2] - 1 ], List( deduped_20_1[deduped_2_2][2], function ( objC_3 )
                      return deduped_16_1[1 + deduped_15_1[(1 + IndexOfObject( objC_3 ))]];
                  end ) );
        end );
    hoisted_13_1 := List( deduped_68_1, function ( logic_new_func_x_2 )
            return Length( Source( logic_new_func_x_2 ) );
        end );
    hoisted_12_1 := List( deduped_68_1, AsList );
    deduped_17_1 := List( deduped_58_1, function ( m_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + m_2;
            return NTuple( 2, hoisted_12_1[deduped_1_2], ListWithIdenticalEntries( hoisted_13_1[deduped_1_2], deduped_16_1[1 + deduped_15_1[(1 + deduped_6_1[deduped_1_2])]] ) );
        end );
    hoisted_30_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := 1 + i_2;
              hoisted_2_2 := deduped_21_1[deduped_3_2][1];
              hoisted_1_2 := deduped_17_1[deduped_3_2][1];
              return List( [ 0 .. deduped_8_1[deduped_3_2][1] - 1 ], function ( i_3 )
                      local hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_54_1[deduped_6_3];
                      deduped_4_3 := Product( deduped_54_1{[ 1 .. deduped_7_3 ]} );
                      hoisted_3_3 := DivIntWithGivenQuotient( deduped_53_1, deduped_4_3, deduped_5_3 * Product( deduped_54_1{[ (deduped_6_3 + 1) .. deduped_28_1 ]} ) );
                      return List( deduped_51_1, function ( i_4 )
                              return RemIntWithDomain( QuoIntWithDomain( i_4, deduped_4_3, deduped_53_1 ), deduped_5_3, hoisted_3_3 );
                          end );
                  end );
          end ) );
    hoisted_26_1 := Concatenation( List( deduped_58_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := 1 + i_2;
              deduped_4_2 := deduped_17_1[deduped_5_2];
              hoisted_3_2 := List( deduped_21_1[deduped_5_2][2], IndexOfMorphism );
              hoisted_2_2 := deduped_4_2[1];
              hoisted_1_2 := List( deduped_4_2[2], IndexOfMorphism );
              return List( [ 0 .. deduped_8_1[deduped_5_2][1] - 1 ], function ( i_3 )
                      local deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3;
                      deduped_11_3 := 1 + i_3;
                      deduped_10_3 := deduped_18_1[1 + hoisted_1_2[deduped_11_3]][1 + hoisted_3_2[(1 + hoisted_2_2[deduped_11_3])]];
                      deduped_9_3 := 1 + deduped_10_3;
                      deduped_8_3 := deduped_23_1[deduped_9_3];
                      deduped_7_3 := deduped_22_1[deduped_9_3];
                      deduped_6_3 := 1 + deduped_7_3;
                      deduped_5_3 := deduped_15_1[deduped_6_3];
                      deduped_4_3 := 1 + deduped_5_3;
                      if CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                  if deduped_7_3 = deduped_22_1[deduped_4_3] and deduped_8_3 = deduped_23_1[deduped_4_3] then
                                      return deduped_10_3 = deduped_5_3;
                                  else
                                      return false;
                                  fi;
                                  return;
                              end )(  ) then
                          return [ 0 .. deduped_2_1[deduped_6_3] - 1 ];
                      else
                          return deduped_25_1[SafeUniquePositionProperty( deduped_24_1, function ( mor_4 )
                                   if IndexOfObject( Source( mor_4 ) ) = deduped_7_3 and IndexOfObject( Range( mor_4 ) ) = deduped_8_3 then
                                       return IndexOfMorphism( mor_4 ) = deduped_10_3;
                                   else
                                       return false;
                                   fi;
                                   return;
                               end )];
                      fi;
                      return;
                  end );
          end ) );
    hoisted_31_1 := List( deduped_52_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2, deduped_3_2;
            deduped_3_2 := 1 + i_2;
            hoisted_2_2 := hoisted_26_1[deduped_3_2];
            hoisted_1_2 := hoisted_30_1[deduped_3_2];
            return List( [ 0 .. deduped_10_1[deduped_3_2] - 1 ], function ( i_3 )
                    return hoisted_2_2[1 + hoisted_1_2[(1 + i_3)]];
                end );
        end );
    deduped_49_1 := Filtered( deduped_51_1, function ( x_2 )
            local deduped_1_2;
            deduped_1_2 := 1 + CAP_JIT_INCOMPLETE_LOGIC( x_2 );
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_50_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_31_1[deduped_1_3][deduped_1_2] * deduped_33_1[deduped_1_3];
                    end ) ) = CAP_JIT_INCOMPLETE_LOGIC( Sum( deduped_50_1, function ( j_3 )
                        local deduped_1_3;
                        deduped_1_3 := 1 + j_3;
                        return hoisted_39_1[deduped_1_3][deduped_1_2] * deduped_33_1[deduped_1_3];
                    end ) );
        end );
    hoisted_47_1 := Target( cat_1 );
    deduped_42_1 := List( deduped_63_1, Length );
    deduped_43_1 := List( deduped_59_1, function ( i_2 )
            return Product( deduped_54_1{[ 1 + Sum( deduped_42_1{[ 1 .. (i_2 - 1) ]} ) .. Sum( deduped_42_1{[ 1 .. i_2 ]} ) ]} );
        end );
    hoisted_45_1 := List( deduped_59_1, function ( i_2 )
            local hoisted_3_2, deduped_4_2, deduped_5_2;
            deduped_5_2 := deduped_43_1[i_2];
            deduped_4_2 := Product( deduped_43_1{[ 1 .. i_2 - 1 ]} );
            hoisted_3_2 := DivIntWithGivenQuotient( deduped_53_1, deduped_4_2, deduped_5_2 * Product( deduped_43_1{[ (i_2 + 1) .. deduped_60_1 ]} ) );
            return List( deduped_51_1, function ( i_3 )
                    return RemIntWithDomain( QuoIntWithDomain( i_3, deduped_4_2, deduped_53_1 ), deduped_5_2, hoisted_3_2 );
                end );
        end );
    return List( [ 0 .. Length( deduped_49_1 ) - 1 ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := 1 + deduped_49_1[(1 + i_2)];
            return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg3_1, ValuesOnAllObjects, List( deduped_59_1, function ( i_3 )
                      local hoisted_1_3, hoisted_3_3, deduped_4_3;
                      deduped_4_3 := deduped_42_1[i_3];
                      hoisted_3_3 := deduped_2_1[i_3];
                      hoisted_1_3 := hoisted_45_1[i_3][hoisted_1_2];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_47_1, deduped_63_1[i_3], deduped_66_1[i_3], AsList, List( [ 0 .. deduped_4_3 - 1 ], function ( i_4 )
                                return DigitInPositionalNotation( hoisted_1_3, i_4, deduped_4_3, hoisted_3_3 );
                            end ) );
                  end ) );
        end );
end
########
        
    , 802 : IsPrecompiledDerivation := true );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "PreSheavesOfCategoryFromDataTablesInSkeletalFinSetsPrecompiled", function ( quiver )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( quiver )
    local sFinSets;
    sFinSets := SkeletalCategoryOfFiniteSets(  : FinalizeCategory := true,
        overhead := true );
    return PreSheaves( CategoryFromDataTables( FreeCategory( quiver : range_of_HomStructure := sFinSets,
            FinalizeCategory := true ) : FinalizeCategory := true ), sFinSets );
end;
        
        
    
    cat := category_constructor( quiver : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_PreSheavesOfCategoryFromDataTablesInSkeletalFinSetsPrecompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
