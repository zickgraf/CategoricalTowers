# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_AdditiveClosureOfAlgebroidOfFiniteDimensionalQuotientOfPathAlgebraOfRightQuiverOverFieldPrecompiled", function ( cat )
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, a_1, b_1 )
    local hoisted_3_1, deduped_4_1, deduped_5_1;
    deduped_4_1 := Source( a_1 );
    deduped_5_1 := MorphismMatrix( a_1 );
    hoisted_3_1 := [ 1 .. NumberColumns( a_1 ) ];
    return AdditiveClosureMorphismListList( deduped_4_1, List( [ 1 .. function (  )
                    if IsMatrixObj( deduped_5_1 ) then
                        return NumberRows( deduped_5_1 );
                    else
                        return Length( ObjectList( deduped_4_1 ) );
                    fi;
                    return;
                end(  ) ], function ( i_2 )
              return List( hoisted_3_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := MatElm( a_1, i_2, j_3 );
                      deduped_1_3 := Source( deduped_2_3 );
                      return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                             ), CapCategory( deduped_1_3 ), deduped_1_3, Range( deduped_2_3 ), UnderlyingQuiverAlgebraElement, UnderlyingQuiverAlgebraElement( deduped_2_3 ) + UnderlyingQuiverAlgebraElement( MatElm( b_1, i_2, j_3 ) ) );
                  end );
          end ), Range( a_1 ) );
end
########
        
    , 100 );
    
    ##
    AddAdditiveInverseForMorphisms( cat,
        
########
function ( cat_1, a_1 )
    local hoisted_1_1, deduped_2_1, deduped_3_1;
    deduped_2_1 := Source( a_1 );
    deduped_3_1 := MorphismMatrix( a_1 );
    hoisted_1_1 := [ 1 .. NumberColumns( a_1 ) ];
    return AdditiveClosureMorphismListList( deduped_2_1, List( [ 1 .. function (  )
                    if IsMatrixObj( deduped_3_1 ) then
                        return NumberRows( deduped_3_1 );
                    else
                        return Length( ObjectList( deduped_2_1 ) );
                    fi;
                    return;
                end(  ) ], function ( i_2 )
              return List( hoisted_1_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := MatElm( a_1, i_2, j_3 );
                      deduped_1_3 := Source( deduped_2_3 );
                      return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                             ), CapCategory( deduped_1_3 ), deduped_1_3, Range( deduped_2_3 ), UnderlyingQuiverAlgebraElement, - UnderlyingQuiverAlgebraElement( deduped_2_3 ) );
                  end );
          end ), Range( a_1 ) );
end
########
        
    , 100 );
    
    ##
    AddDirectSum( cat,
        
########
function ( cat_1, arg2_1 )
    return AdditiveClosureObject( Concatenation( List( arg2_1, ObjectList ) ), cat_1 );
end
########
        
    , 100 );
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( cat,
        
########
function ( cat_1 )
    return ObjectifyObjectForCAPWithAttributes( rec(
           ), RangeCategoryOfHomomorphismStructure( cat_1 ), Dimension, 1 );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, beta_1, range_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1;
    deduped_21_1 := MorphismMatrix( alpha_1 );
    deduped_18_1 := IsMatrixObj( deduped_21_1 );
    deduped_22_1 := Range( alpha_1 );
    deduped_15_1 := [ 1 .. function (  )
                if deduped_18_1 then
                    return NumberColumns( deduped_21_1 );
                else
                    return Length( ObjectList( deduped_22_1 ) );
                fi;
                return;
            end(  ) ];
    deduped_23_1 := Source( alpha_1 );
    deduped_16_1 := [ 1 .. function (  )
                if deduped_18_1 then
                    return NumberRows( deduped_21_1 );
                else
                    return Length( ObjectList( deduped_23_1 ) );
                fi;
                return;
            end(  ) ];
    deduped_20_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
    deduped_17_1 := UnderlyingRing( deduped_20_1 );
    deduped_26_1 := MorphismMatrix( beta_1 );
    deduped_19_1 := IsMatrixObj( deduped_26_1 );
    deduped_24_1 := UnderlyingCategory( cat_1 );
    deduped_25_1 := Source( beta_1 );
    deduped_27_1 := Range( beta_1 );
    hoisted_1_1 := deduped_22_1;
    hoisted_2_1 := BasisPathsByVertexIndex( deduped_24_1 );
    hoisted_4_1 := deduped_20_1;
    hoisted_7_1 := deduped_23_1;
    hoisted_8_1 := deduped_27_1;
    hoisted_9_1 := [ 1 .. function (  )
                if deduped_19_1 then
                    return NumberColumns( deduped_26_1 );
                else
                    return Length( ObjectList( deduped_27_1 ) );
                fi;
                return;
            end(  ) ];
    hoisted_10_1 := List( deduped_16_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_2_1[VertexIndex( UnderlyingVertex( hoisted_7_1[i_2] ) )];
            return List( hoisted_9_1, function ( t_3 )
                    return ObjectifyObjectForCAPWithAttributes( rec(
                           ), hoisted_4_1, Dimension, Length( hoisted_1_2[VertexIndex( UnderlyingVertex( hoisted_8_1[t_3] ) )] ) );
                end );
        end );
    hoisted_11_1 := List( deduped_16_1, function ( logic_new_func_x_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_10_1[logic_new_func_x_2];
            return Sum( List( hoisted_9_1, function ( logic_new_func_x_3 )
                      return Dimension( hoisted_1_2[logic_new_func_x_3] );
                  end ) );
        end );
    hoisted_12_1 := deduped_17_1;
    hoisted_13_1 := HomStructureOnBasisPaths( deduped_24_1 );
    hoisted_14_1 := deduped_16_1;
    hoisted_3_1 := deduped_25_1;
    hoisted_5_1 := [ 1 .. function (  )
                if deduped_19_1 then
                    return NumberRows( deduped_26_1 );
                else
                    return Length( ObjectList( deduped_25_1 ) );
                fi;
                return;
            end(  ) ];
    hoisted_6_1 := List( deduped_15_1, function ( j_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_2_1[VertexIndex( UnderlyingVertex( hoisted_1_1[j_2] ) )];
            return List( hoisted_5_1, function ( s_3 )
                    return ObjectifyObjectForCAPWithAttributes( rec(
                           ), hoisted_4_1, Dimension, Length( hoisted_1_2[VertexIndex( UnderlyingVertex( hoisted_3_1[s_3] ) )] ) );
                end );
        end );
    return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
           ), deduped_20_1, source_1, range_1, UnderlyingMatrix, UnionOfRows( deduped_17_1, Dimension( range_1 ), List( deduped_15_1, function ( logic_new_func_x_2 )
                local hoisted_1_2, hoisted_2_2;
                hoisted_1_2 := hoisted_6_1[logic_new_func_x_2];
                hoisted_2_2 := Sum( hoisted_5_1, function ( logic_new_func_x_3 )
                        return Dimension( hoisted_1_2[logic_new_func_x_3] );
                    end );
                return UnionOfColumns( hoisted_12_1, Sum( List( hoisted_5_1, function ( logic_new_func_x_3 )
                            return Dimension( hoisted_1_2[logic_new_func_x_3] );
                        end ) ), List( hoisted_14_1, function ( logic_new_func_x_3 )
                          local hoisted_1_3, hoisted_2_3, hoisted_3_3, hoisted_4_3, hoisted_5_3, hoisted_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3, deduped_12_3;
                          deduped_11_3 := MatElm( alpha_1, logic_new_func_x_3, logic_new_func_x_2 );
                          deduped_10_3 := UnderlyingQuiverAlgebraElement( deduped_11_3 );
                          deduped_12_3 := hoisted_11_1[logic_new_func_x_3];
                          if IsZero( deduped_10_3 ) then
                              return HomalgZeroMatrix( hoisted_2_2, deduped_12_3, hoisted_12_1 );
                          else
                              deduped_8_3 := VertexIndex( UnderlyingVertex( Source( deduped_11_3 ) ) );
                              deduped_9_3 := VertexIndex( UnderlyingVertex( Range( deduped_11_3 ) ) );
                              deduped_7_3 := hoisted_2_1[deduped_8_3][deduped_9_3];
                              hoisted_1_3 := hoisted_10_1[logic_new_func_x_3];
                              hoisted_2_3 := Sum( hoisted_9_1, function ( logic_new_func_x_4 )
                                      return Dimension( hoisted_1_3[logic_new_func_x_4] );
                                  end );
                              hoisted_3_3 := CoefficientsOfPaths( deduped_7_3, deduped_10_3 );
                              hoisted_4_3 := hoisted_13_1[deduped_9_3];
                              hoisted_5_3 := deduped_8_3;
                              hoisted_6_3 := [ 1 .. Length( deduped_7_3 ) ];
                              return UnionOfRows( hoisted_12_1, deduped_12_3, List( hoisted_5_1, function ( logic_new_func_x_4 )
                                        local hoisted_1_4, deduped_2_4;
                                        deduped_2_4 := Dimension( hoisted_1_2[logic_new_func_x_4] );
                                        if deduped_2_4 = 0 then
                                            return HomalgZeroMatrix( deduped_2_4, hoisted_2_3, hoisted_12_1 );
                                        else
                                            hoisted_1_4 := deduped_2_4;
                                            return UnionOfColumns( hoisted_12_1, deduped_2_4, List( hoisted_9_1, function ( logic_new_func_x_5 )
                                                      local hoisted_1_5, hoisted_2_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5, deduped_7_5, deduped_8_5, deduped_9_5;
                                                      deduped_9_5 := MatElm( beta_1, logic_new_func_x_4, logic_new_func_x_5 );
                                                      deduped_7_5 := UnderlyingQuiverAlgebraElement( deduped_9_5 );
                                                      deduped_8_5 := Dimension( hoisted_1_3[logic_new_func_x_5] );
                                                      if IsZero( deduped_7_5 ) or deduped_8_5 = 0 then
                                                          return HomalgZeroMatrix( hoisted_1_4, deduped_8_5, hoisted_12_1 );
                                                      else
                                                          deduped_5_5 := VertexIndex( UnderlyingVertex( Source( deduped_9_5 ) ) );
                                                          deduped_6_5 := VertexIndex( UnderlyingVertex( Range( deduped_9_5 ) ) );
                                                          deduped_4_5 := hoisted_2_1[deduped_5_5][deduped_6_5];
                                                          hoisted_1_5 := CoefficientsOfPaths( deduped_4_5, deduped_7_5 );
                                                          hoisted_2_5 := hoisted_4_3[deduped_5_5][hoisted_5_3][deduped_6_5];
                                                          hoisted_3_5 := [ 1 .. Length( deduped_4_5 ) ];
                                                          return HomalgMatrix( Sum( hoisted_6_3, function ( p_6 )
                                                                    local hoisted_1_6, hoisted_2_6;
                                                                    hoisted_1_6 := hoisted_3_3[p_6];
                                                                    hoisted_2_6 := hoisted_2_5[p_6];
                                                                    return Sum( hoisted_3_5, function ( q_7 )
                                                                            return hoisted_1_6 * hoisted_1_5[q_7] * hoisted_2_6[q_7];
                                                                        end );
                                                                end ), hoisted_1_4, deduped_8_5, hoisted_12_1 );
                                                      fi;
                                                      return;
                                                  end ) );
                                        fi;
                                        return;
                                    end ) );
                          fi;
                          return;
                      end ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1;
    hoisted_3_1 := BasisPathsByVertexIndex( UnderlyingCategory( cat_1 ) );
    hoisted_4_1 := ObjectList( arg3_1 );
    return ObjectifyObjectForCAPWithAttributes( rec(
           ), RangeCategoryOfHomomorphismStructure( cat_1 ), Dimension, Sum( Concatenation( List( ObjectList( arg2_1 ), function ( logic_new_func_x_2 )
                  local hoisted_1_2;
                  hoisted_1_2 := hoisted_3_1[VertexIndex( UnderlyingVertex( logic_new_func_x_2 ) )];
                  return List( hoisted_4_1, function ( logic_new_func_x_3 )
                          return Length( hoisted_1_2[VertexIndex( UnderlyingVertex( logic_new_func_x_3 ) )] );
                      end );
              end ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := ObjectList( a_1 );
    deduped_5_1 := [ 1 .. Length( deduped_7_1 ) ];
    deduped_6_1 := UnderlyingQuiverAlgebra( UnderlyingCategory( cat_1 ) );
    hoisted_1_1 := deduped_7_1;
    hoisted_2_1 := deduped_6_1;
    hoisted_3_1 := ZeroImmutable( deduped_6_1 );
    hoisted_4_1 := deduped_5_1;
    return AdditiveClosureMorphismListList( a_1, List( deduped_5_1, function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := hoisted_1_1[i_2];
              deduped_4_2 := CapCategory( deduped_5_2 );
              hoisted_1_2 := ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                     ), deduped_4_2, deduped_5_2, deduped_5_2, UnderlyingQuiverAlgebraElement, PathAsAlgebraElement( hoisted_2_1, UnderlyingVertex( deduped_5_2 ) ) );
              hoisted_2_2 := deduped_4_2;
              hoisted_3_2 := deduped_5_2;
              return List( hoisted_4_1, function ( j_3 )
                      if i_2 = j_3 then
                          return hoisted_1_2;
                      else
                          return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                                 ), hoisted_2_2, hoisted_3_2, hoisted_1_1[j_3], UnderlyingQuiverAlgebraElement, hoisted_3_1 );
                      fi;
                      return;
                  end );
          end ), a_1 );
end
########
        
    , 100 );
    
    ##
    AddInterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructureWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, range_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_7_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
    deduped_5_1 := UnderlyingRing( deduped_7_1 );
    deduped_9_1 := MorphismMatrix( alpha_1 );
    deduped_6_1 := IsMatrixObj( deduped_9_1 );
    deduped_8_1 := Dimension( source_1 );
    hoisted_1_1 := BasisPathsByVertexIndex( UnderlyingCategory( cat_1 ) );
    hoisted_2_1 := deduped_5_1;
    hoisted_3_1 := [ 1 .. function (  )
                if deduped_6_1 then
                    return NumberColumns( deduped_9_1 );
                else
                    return Length( ObjectList( Range( alpha_1 ) ) );
                fi;
                return;
            end(  ) ];
    hoisted_4_1 := deduped_8_1;
    return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
           ), deduped_7_1, source_1, range_1, UnderlyingMatrix, UnionOfColumns( deduped_5_1, deduped_8_1, List( [ 1 .. function (  )
                      if deduped_6_1 then
                          return NumberRows( deduped_9_1 );
                      else
                          return Length( ObjectList( Source( alpha_1 ) ) );
                      fi;
                      return;
                  end(  ) ], function ( logic_new_func_x_2 )
                return UnionOfColumns( hoisted_2_1, hoisted_4_1, List( hoisted_3_1, function ( logic_new_func_x_3 )
                          local deduped_1_3, deduped_2_3, deduped_3_3;
                          deduped_3_3 := MatElm( alpha_1, logic_new_func_x_2, logic_new_func_x_3 );
                          deduped_2_3 := hoisted_1_1[VertexIndex( UnderlyingVertex( Source( deduped_3_3 ) ) )][VertexIndex( UnderlyingVertex( Range( deduped_3_3 ) ) )];
                          deduped_1_3 := Length( deduped_2_3 );
                          if deduped_1_3 = 0 then
                              return HomalgZeroMatrix( 1, deduped_1_3, hoisted_2_1 );
                          else
                              return HomalgMatrix( CoefficientsOfPaths( deduped_2_3, Representative( UnderlyingQuiverAlgebraElement( deduped_3_3 ) ) ), 1, deduped_1_3, hoisted_2_1 );
                          fi;
                          return;
                      end ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
        
########
function ( cat_1, arg2_1, arg3_1, arg4_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1;
    deduped_18_1 := ObjectList( arg2_1 );
    deduped_15_1 := Length( deduped_18_1 );
    deduped_14_1 := [ 1 .. deduped_15_1 ];
    deduped_19_1 := ObjectList( arg3_1 );
    deduped_16_1 := Length( deduped_19_1 );
    deduped_20_1 := UnderlyingCategory( cat_1 );
    deduped_17_1 := UnderlyingQuiverAlgebra( deduped_20_1 );
    hoisted_1_1 := deduped_18_1;
    hoisted_2_1 := deduped_19_1;
    hoisted_4_1 := [ 1 .. deduped_16_1 ];
    if deduped_15_1 = 0 or deduped_16_1 = 0 then
        hoisted_3_1 := ZeroImmutable( deduped_17_1 );
        return AdditiveClosureMorphismListList( arg2_1, List( deduped_14_1, function ( i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2;
                  deduped_3_2 := hoisted_1_1[i_2];
                  hoisted_1_2 := CapCategory( deduped_3_2 );
                  hoisted_2_2 := deduped_3_2;
                  return List( hoisted_4_1, function ( j_3 )
                          return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                                 ), hoisted_1_2, hoisted_2_2, hoisted_2_1[j_3], UnderlyingQuiverAlgebraElement, hoisted_3_1 );
                      end );
              end ), arg3_1 );
    else
        hoisted_10_1 := UnderlyingMatrix( arg4_1 );
        hoisted_11_1 := Source( arg4_1 );
        hoisted_5_1 := BasisPathsByVertexIndex( deduped_20_1 );
        hoisted_6_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
        hoisted_7_1 := deduped_16_1;
        hoisted_8_1 := Concatenation( List( deduped_18_1, function ( obj_i_2 )
                  local hoisted_1_2;
                  hoisted_1_2 := hoisted_5_1[VertexIndex( UnderlyingVertex( obj_i_2 ) )];
                  return List( hoisted_2_1, function ( obj_j_3 )
                          return ObjectifyObjectForCAPWithAttributes( rec(
                                 ), hoisted_6_1, Dimension, Length( hoisted_1_2[VertexIndex( UnderlyingVertex( obj_j_3 ) )] ) );
                      end );
              end ) );
        hoisted_9_1 := Concatenation( List( deduped_18_1, function ( logic_new_func_x_2 )
                  local hoisted_1_2;
                  hoisted_1_2 := hoisted_5_1[VertexIndex( UnderlyingVertex( logic_new_func_x_2 ) )];
                  return List( hoisted_2_1, function ( logic_new_func_x_3 )
                          return Length( hoisted_1_2[VertexIndex( UnderlyingVertex( logic_new_func_x_3 ) )] );
                      end );
              end ) );
        hoisted_12_1 := List( deduped_14_1, function ( i_2 )
                local hoisted_1_2;
                hoisted_1_2 := hoisted_7_1 * (i_2 - 1);
                return List( hoisted_4_1, function ( j_3 )
                        local deduped_1_3, deduped_2_3;
                        deduped_2_3 := hoisted_1_2 + j_3;
                        deduped_1_3 := Sum( hoisted_9_1{[ 1 .. deduped_2_3 - 1 ]} ) + 1;
                        return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                               ), hoisted_6_1, hoisted_11_1, hoisted_8_1[deduped_2_3], UnderlyingMatrix, CertainColumns( hoisted_10_1, [ deduped_1_3 .. deduped_1_3 - 1 + hoisted_9_1[deduped_2_3] ] ) );
                    end );
            end );
        hoisted_13_1 := deduped_17_1;
        return AdditiveClosureMorphismListList( arg2_1, List( deduped_14_1, function ( i_2 )
                  local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, deduped_5_2;
                  deduped_5_2 := hoisted_1_1[i_2];
                  hoisted_1_2 := hoisted_12_1[i_2];
                  hoisted_2_2 := hoisted_5_1[VertexIndex( UnderlyingVertex( deduped_5_2 ) )];
                  hoisted_3_2 := CapCategory( deduped_5_2 );
                  hoisted_4_2 := deduped_5_2;
                  return List( hoisted_4_1, function ( j_3 )
                          local deduped_1_3;
                          deduped_1_3 := hoisted_2_1[j_3];
                          return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                                 ), hoisted_3_2, hoisted_4_2, deduped_1_3, UnderlyingQuiverAlgebraElement, QuiverAlgebraElement( hoisted_13_1, EntriesOfHomalgMatrix( UnderlyingMatrix( hoisted_1_2[j_3] ) ), hoisted_2_2[VertexIndex( UnderlyingVertex( deduped_1_3 ) )] ) );
                      end );
              end ), arg3_1 );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_8_1 := MorphismMatrix( arg2_1 );
    deduped_6_1 := IsMatrixObj( deduped_8_1 );
    if deduped_6_1 then
        deduped_4_1 := NumberRows( deduped_8_1 );
    else
        deduped_4_1 := Length( ObjectList( Source( arg2_1 ) ) );
    fi;
    if deduped_6_1 then
        deduped_5_1 := NumberColumns( deduped_8_1 );
    else
        deduped_5_1 := Length( ObjectList( Range( arg2_1 ) ) );
    fi;
    deduped_9_1 := MorphismMatrix( arg3_1 );
    deduped_7_1 := IsMatrixObj( deduped_9_1 );
    if deduped_4_1 <> function (  )
                if deduped_7_1 then
                    return NumberRows( deduped_9_1 );
                else
                    return Length( ObjectList( Source( arg3_1 ) ) );
                fi;
                return;
            end(  ) then
        return false;
    elif deduped_5_1 <> function (  )
                if deduped_7_1 then
                    return NumberColumns( deduped_9_1 );
                else
                    return Length( ObjectList( Range( arg3_1 ) ) );
                fi;
                return;
            end(  ) then
        return false;
    elif deduped_4_1 = 0 or deduped_5_1 = 0 then
        return true;
    else
        hoisted_3_1 := [ 1 .. deduped_5_1 ];
        return ForAll( [ 1 .. deduped_4_1 ], function ( i_2 )
                return ForAll( hoisted_3_1, function ( j_3 )
                        return UnderlyingQuiverAlgebraElement( MatElm( arg2_1, i_2, j_3 ) ) = UnderlyingQuiverAlgebraElement( MatElm( arg3_1, i_2, j_3 ) );
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsEqualForCacheForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return IS_IDENTICAL_OBJ( arg2_1, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsEqualForCacheForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return IS_IDENTICAL_OBJ( arg2_1, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_8_1 := MorphismMatrix( arg2_1 );
    deduped_6_1 := IsMatrixObj( deduped_8_1 );
    if deduped_6_1 then
        deduped_4_1 := NumberRows( deduped_8_1 );
    else
        deduped_4_1 := Length( ObjectList( Source( arg2_1 ) ) );
    fi;
    if deduped_6_1 then
        deduped_5_1 := NumberColumns( deduped_8_1 );
    else
        deduped_5_1 := Length( ObjectList( Range( arg2_1 ) ) );
    fi;
    deduped_9_1 := MorphismMatrix( arg3_1 );
    deduped_7_1 := IsMatrixObj( deduped_9_1 );
    if deduped_4_1 <> function (  )
                if deduped_7_1 then
                    return NumberRows( deduped_9_1 );
                else
                    return Length( ObjectList( Source( arg3_1 ) ) );
                fi;
                return;
            end(  ) then
        return false;
    elif deduped_5_1 <> function (  )
                if deduped_7_1 then
                    return NumberColumns( deduped_9_1 );
                else
                    return Length( ObjectList( Range( arg3_1 ) ) );
                fi;
                return;
            end(  ) then
        return false;
    elif deduped_4_1 = 0 or deduped_5_1 = 0 then
        return true;
    else
        hoisted_3_1 := [ 1 .. deduped_5_1 ];
        return ForAll( [ 1 .. deduped_4_1 ], function ( i_2 )
                return ForAll( hoisted_3_1, function ( j_3 )
                        return UnderlyingQuiverAlgebraElement( MatElm( arg2_1, i_2, j_3 ) ) = UnderlyingQuiverAlgebraElement( MatElm( arg3_1, i_2, j_3 ) );
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_6_1 := ObjectList( arg2_1 );
    deduped_5_1 := Length( deduped_6_1 );
    deduped_7_1 := ObjectList( arg3_1 );
    if deduped_5_1 <> Length( deduped_7_1 ) then
        return false;
    else
        hoisted_3_1 := deduped_6_1;
        hoisted_4_1 := deduped_7_1;
        return ForAll( [ 1 .. deduped_5_1 ], function ( i_2 )
                return UnderlyingVertex( hoisted_3_1[i_2] ) = UnderlyingVertex( hoisted_4_1[i_2] );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := MorphismMatrix( arg2_1 );
    deduped_8_1 := ObjectList( Source( arg2_1 ) );
    deduped_6_1 := Length( deduped_8_1 );
    deduped_5_1 := [ 1 .. deduped_6_1 ];
    deduped_9_1 := ObjectList( Range( arg2_1 ) );
    deduped_7_1 := Length( deduped_9_1 );
    hoisted_1_1 := [ 1 .. deduped_7_1 ];
    hoisted_2_1 := UnderlyingCategory( cat_1 );
    hoisted_3_1 := deduped_8_1;
    hoisted_4_1 := deduped_9_1;
    if IsMatrixObj( deduped_10_1 ) and not (deduped_6_1 = NumberRows( deduped_10_1 ) and deduped_7_1 = NumberColumns( deduped_10_1 )) then
        return false;
    elif not ForAll( deduped_5_1, function ( i_2 )
                 return ForAll( hoisted_1_1, function ( j_3 )
                         return IsCapCategoryMorphism( MatElm( arg2_1, i_2, j_3 ) );
                     end );
             end ) then
        return false;
    elif not ForAll( deduped_5_1, function ( i_2 )
                 return ForAll( hoisted_1_1, function ( j_3 )
                         return IS_IDENTICAL_OBJ( hoisted_2_1, CapCategory( MatElm( arg2_1, i_2, j_3 ) ) );
                     end );
             end ) then
        return false;
    elif not ForAll( deduped_5_1, function ( i_2 )
                 local hoisted_1_2;
                 hoisted_1_2 := UnderlyingVertex( hoisted_3_1[i_2] );
                 return ForAll( hoisted_1_1, function ( j_3 )
                         local deduped_1_3;
                         deduped_1_3 := MatElm( arg2_1, i_2, j_3 );
                         return (UnderlyingVertex( Source( deduped_1_3 ) ) = hoisted_1_2 and UnderlyingVertex( Range( deduped_1_3 ) ) = UnderlyingVertex( hoisted_4_1[j_3] ));
                     end );
             end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1;
    hoisted_1_1 := UnderlyingCategory( cat_1 );
    if not ForAll( ObjectList( arg2_1 ), function ( obj_2 )
                 return IS_IDENTICAL_OBJ( hoisted_1_1, CapCategory( obj_2 ) );
             end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsZeroForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, deduped_2_1;
    deduped_2_1 := MorphismMatrix( arg2_1 );
    hoisted_1_1 := [ 1 .. NumberColumns( arg2_1 ) ];
    return ForAll( [ 1 .. function (  )
                  if IsMatrixObj( deduped_2_1 ) then
                      return NumberRows( deduped_2_1 );
                  else
                      return Length( ObjectList( Source( arg2_1 ) ) );
                  fi;
                  return;
              end(  ) ], function ( i_2 )
            return ForAll( hoisted_1_1, function ( j_3 )
                    return IsZero( UnderlyingQuiverAlgebraElement( MatElm( arg2_1, i_2, j_3 ) ) );
                end );
        end );
end
########
        
    , 100 );
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( cat,
        
########
function ( cat_1, r_1, a_1 )
    local hoisted_1_1;
    hoisted_1_1 := [ 1 .. NumberColumns( a_1 ) ];
    return AdditiveClosureMorphismListList( Source( a_1 ), List( [ 1 .. NumberRows( a_1 ) ], function ( i_2 )
              return List( hoisted_1_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := MatElm( a_1, i_2, j_3 );
                      deduped_1_3 := Source( deduped_2_3 );
                      return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                             ), CapCategory( deduped_1_3 ), deduped_1_3, Range( deduped_2_3 ), UnderlyingQuiverAlgebraElement, r_1 * UnderlyingQuiverAlgebraElement( deduped_2_3 ) );
                  end );
          end ), Range( a_1 ) );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_14_1 := Source( alpha_1 );
    deduped_15_1 := Range( beta_1 );
    deduped_12_1 := MorphismMatrix( alpha_1 );
    deduped_13_1 := MorphismMatrix( beta_1 );
    if IsMatrixObj( deduped_12_1 ) then
        deduped_9_1 := NumberColumns( deduped_12_1 );
    else
        deduped_9_1 := Length( ObjectList( Range( alpha_1 ) ) );
    fi;
    if ForAny( [ deduped_9_1, function (  )
                    if IsMatrixObj( deduped_13_1 ) then
                        return NumberRows( deduped_13_1 );
                    else
                        return Length( ObjectList( Source( beta_1 ) ) );
                    fi;
                    return;
                end(  ) ], IsZero ) then
        deduped_10_1 := ObjectList( deduped_14_1 );
        deduped_11_1 := ObjectList( deduped_15_1 );
        hoisted_3_1 := deduped_10_1;
        hoisted_4_1 := deduped_11_1;
        hoisted_5_1 := ZeroImmutable( UnderlyingQuiverAlgebra( UnderlyingCategory( cat_1 ) ) );
        hoisted_6_1 := [ 1 .. Length( deduped_11_1 ) ];
        return AdditiveClosureMorphismListList( deduped_14_1, List( [ 1 .. Length( deduped_10_1 ) ], function ( i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2;
                  deduped_3_2 := hoisted_3_1[i_2];
                  hoisted_1_2 := CapCategory( deduped_3_2 );
                  hoisted_2_2 := deduped_3_2;
                  return List( hoisted_6_1, function ( j_3 )
                          return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                                 ), hoisted_1_2, hoisted_2_2, hoisted_4_1[j_3], UnderlyingQuiverAlgebraElement, hoisted_5_1 );
                      end );
              end ), deduped_15_1 );
    else
        hoisted_7_1 := [ 1 .. deduped_9_1 ];
        hoisted_8_1 := [ 1 .. NumberColumns( beta_1 ) ];
        return AdditiveClosureMorphismListList( deduped_14_1, List( [ 1 .. NumberRows( alpha_1 ) ], function ( i_2 )
                  return List( hoisted_8_1, function ( j_3 )
                          return Sum( List( hoisted_7_1, function ( k_4 )
                                    local deduped_1_4, deduped_2_4, deduped_3_4;
                                    deduped_2_4 := MatElm( alpha_1, i_2, k_4 );
                                    deduped_1_4 := Source( deduped_2_4 );
                                    deduped_3_4 := MatElm( beta_1, k_4, j_3 );
                                    return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                                           ), CapCategory( deduped_1_4 ), deduped_1_4, Range( deduped_3_4 ), UnderlyingQuiverAlgebraElement, UnderlyingQuiverAlgebraElement( deduped_2_4 ) * UnderlyingQuiverAlgebraElement( deduped_3_4 ) );
                                end ) );
                      end );
              end ), deduped_15_1 );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismFromDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    return AdditiveClosureMorphismListList( P_1, Concatenation( List( tau_1, function ( tau_2 )
                local hoisted_1_2, deduped_2_2;
                deduped_2_2 := MorphismMatrix( tau_2 );
                hoisted_1_2 := [ 1 .. NumberColumns( tau_2 ) ];
                return List( [ 1 .. function (  )
                              if IsMatrixObj( deduped_2_2 ) then
                                  return NumberRows( deduped_2_2 );
                              else
                                  return Length( ObjectList( Source( tau_2 ) ) );
                              fi;
                              return;
                          end(  ) ], function ( i_3 )
                        return List( hoisted_1_2, function ( j_4 )
                                return MatElm( tau_2, i_3, j_4 );
                            end );
                    end );
            end ) ), T_1 );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismIntoDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := tau_1[1];
    deduped_1_1 := MorphismMatrix( deduped_2_1 );
    return AdditiveClosureMorphismListList( T_1, List( [ 1 .. function (  )
                    if IsMatrixObj( deduped_1_1 ) then
                        return NumberRows( deduped_1_1 );
                    else
                        return Length( ObjectList( Source( deduped_2_1 ) ) );
                    fi;
                    return;
                end(  ) ], function ( i_2 )
              return Concatenation( List( tau_1, function ( tau_3 )
                        return List( [ 1 .. NumberColumns( tau_3 ) ], function ( j_4 )
                                return MatElm( tau_3, i_2, j_4 );
                            end );
                    end ) );
          end ), P_1 );
end
########
        
    , 100 );
    
    ##
    AddZeroMorphism( cat,
        
########
function ( cat_1, a_1, b_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1;
    deduped_5_1 := ObjectList( a_1 );
    deduped_6_1 := ObjectList( b_1 );
    hoisted_1_1 := deduped_5_1;
    hoisted_2_1 := deduped_6_1;
    hoisted_3_1 := ZeroImmutable( UnderlyingQuiverAlgebra( UnderlyingCategory( cat_1 ) ) );
    hoisted_4_1 := [ 1 .. Length( deduped_6_1 ) ];
    return AdditiveClosureMorphismListList( a_1, List( [ 1 .. Length( deduped_5_1 ) ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2;
              deduped_3_2 := hoisted_1_1[i_2];
              hoisted_1_2 := CapCategory( deduped_3_2 );
              hoisted_2_2 := deduped_3_2;
              return List( hoisted_4_1, function ( j_3 )
                      return ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec(
                             ), hoisted_1_2, hoisted_2_2, hoisted_2_1[j_3], UnderlyingQuiverAlgebraElement, hoisted_3_1 );
                  end );
          end ), b_1 );
end
########
        
    , 100 );
    
    ##
    AddZeroObject( cat,
        
########
function ( cat_1 )
    return AdditiveClosureObject( [  ], cat_1 );
end
########
        
    , 100 );
    
end );

BindGlobal( "AdditiveClosureOfAlgebroidOfFiniteDimensionalQuotientOfPathAlgebraOfRightQuiverOverFieldPrecompiled", function ( Rq )
  local category_constructor, cat;
    
    category_constructor := 
        
        
        function ( Rq )
    return AdditiveClosure( Algebroid( Rq, false : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor( Rq : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_AdditiveClosureOfAlgebroidOfFiniteDimensionalQuotientOfPathAlgebraOfRightQuiverOverFieldPrecompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
