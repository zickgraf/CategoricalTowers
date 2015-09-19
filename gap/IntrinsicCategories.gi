#############################################################################
##
##  Categories.gd                                IntrinsicCategories package
##
##  Copyright 2015,      Mohamed Barakat, RWTH Aachen University
##
##  Implementation stuff for intrinsic categories.
##
#############################################################################

####################################
#
# representations:
#
####################################

DeclareRepresentation( "IsIntrinsicObjectRep",
        IsCapCategoryObject and IsCapCategoryIntrinsicCell,
        [ ] );

DeclareRepresentation( "IsIntrinsicMorphismRep",
        IsCapCategoryMorphism and IsCapCategoryIntrinsicCell,
        [ ] );

####################################
#
# families and types:
#
####################################

# new families:
BindGlobal( "TheFamilyOfIntrinsicObjects",
        NewFamily( "TheFamilyOfIntrinsicObjects" ) );

BindGlobal( "TheFamilyOfIntrinsicMorphisms",
        NewFamily( "TheFamilyOfIntrinsicMorphisms" ) );

# new types:
BindGlobal( "TheTypeIntrinsicObject",
        NewType( TheFamilyOfIntrinsicObjects,
                IsIntrinsicObjectRep ) );

BindGlobal( "TheTypeIntrinsicMorphism",
        NewType( TheFamilyOfIntrinsicMorphisms,
                IsIntrinsicMorphismRep ) );

####################################
#
# methods for operations:
#
####################################

##
InstallMethod( Intrinsify,
        [ IsCapCategoryObject ],
        
  function( obj )
    
    obj := rec(
               PositionOfActiveCell := 1,
               1 := obj
               );
    
    Objectify( TheTypeIntrinsicObject, obj );
    
    return obj;
    
end );

##
InstallMethod( Intrinsify,
        [ IsCapCategory, IsCapCategoryObject ],
        
  function( C, obj )
    
    obj := Intrinsify( obj );
    
    AddObject( C, obj );
    
    return obj;
    
end );

##
InstallMethod( Intrinsify,
        [ IsCapCategoryMorphism ],
        
  function( mor )
    local S, T;
    
    S := Source( mor );
    T := Range( mor );
    
    if IsEqualForObjects( S, T ) then
        S := Intrinsify( S );
        T := S;
    else        
        S := Intrinsify( S );
        T := Intrinsify( T );
    fi;
    
    return Intrinsify( mor, S, 1, T, 1 );
    
end );

##
InstallMethod( Intrinsify,
        [ IsCapCategory, IsCapCategoryMorphism ],
        
  function( C, mor )
    
    mor := Intrinsify( mor );
    
    AddMorphism( C, mor );
    
    return mor;
    
end );

##
InstallMethod( Intrinsify,
        [ IsCapCategoryMorphism, IsCapCategoryObject, IsInt, IsCapCategoryObject, IsInt ],
        
  function( mor, S, posS, T, posT )
    
    if not IsEqualForObjects( Source( mor ), CertainCell( S, posS ) ) then
        Error( "the source of the morphism is not equal to the specified cell in the given intrinsic source\n" );
    elif not IsEqualForObjects( Range( mor ), CertainCell( T, posT ) ) then
        Error( "the target of the morphism is not equal to the specified cell in the given intrinsic target\n" );
    fi;
    
    mor := rec(
               index_pairs_of_presentations := [ 1, 1 ],
               ("[ 1, 1 ]") := mor
               );
    
    Objectify( TheTypeIntrinsicMorphism, mor );
    
    SetSource( mor, S );
    SetRange( mor, T );
    
    return mor;
    
end );

##
InstallMethod( Intrinsify,
        [ IsCapCategory, IsCapCategoryMorphism, IsCapCategoryObject, IsInt, IsCapCategoryObject, IsInt ],
        
  function( C, mor, S, posS, T, posT )
    
    mor := Intrinsify( mor, S, posS, T, posT );
    
    AddMorphism( C, mor );
    
    return mor;
    
end );
    
##
InstallMethod( PositionOfActiveCell,
        "for an intrinsic object",
        [ IsCapCategoryIntrinsicCell and IsCapCategoryObject ],
        
  obj ->  obj!.PositionOfActiveCell );

##
InstallMethod( CertainCell,
        "for an intrinsic object and an integer",
        [ IsCapCategoryIntrinsicCell and IsCapCategoryObject, IsInt ],
        
  function( obj, pos )
    
    return obj!.(pos);
    
end );

##
InstallMethod( CertainCell,
        "for an intrinsic morphism and two integers",
        [ IsCapCategoryIntrinsicCell and IsCapCategoryMorphism, IsInt, IsInt ],
        
  function( mor, pos_s, pos_t )
    local pos;
    
    pos := [ pos_s, pos_t ];
    
    return mor!.(String( pos ) );
    
end );

##
InstallMethod( ActiveCell,
        "for an intrinsic object",
        [ IsCapCategoryIntrinsicCell and IsCapCategoryObject ],
        
  obj -> CertainCell( obj, PositionOfActiveCell( obj ) ) );

##
InstallMethod( ActiveCell,
        "for an intrinsic morphism",
        [ IsCapCategoryIntrinsicCell and IsCapCategoryMorphism ],
        
  function( mor )
    
    return CertainCell( mor,
                   PositionOfActiveCell( Source( mor ) ),
                   PositionOfActiveCell( Range( mor ) ) );
    
end );

##
InstallMethod( ActiveCell,
        "for a list",
        [ IsList ],
        
  function( L )
    
    return List( L, ActiveCell );
    
end );

##
InstallMethod( ActiveCell,
        "fallback method",
        [ IsObject ],
        
  IdFunc );

##
InstallMethod( IntrinsicCategory,
        [ IsCapCategory ],
        
  function( C )
    local name, IC, recnames, func, pos, create_func_bool,
          create_func_object0, create_func_object, create_func_morphism,
          info, add;
    
    if HasName( C ) then
        name := Concatenation( "intrinsic_", Name( C ) );
        IC := CreateCapCategory( name );
    else
        IC := CreateCapCategory( );
    fi;
    
    IC!.UnderlyingCategory := C;
    
    for name in ListKnownCategoricalProperties( C ) do
        name := ValueGlobal( name );
        Setter( name )( IC, true );
    od;
    
    ## this can be seen as a characterization of the intrinsic categories
    AddIsEqualForObjects( IC, IsIdenticalObj );
    AddIsEqualForMorphisms( IC,
            function( m, n )
              return IsCongruentForMorphisms( ActiveCell( m ), ActiveCell( n ) );
            end
        );
    
    ## TODO: remove `Primitively' for performance?
    recnames := ShallowCopy( ListPrimitivelyInstalledOperationsOfCategory( C ) );
    
    for func in [
            "IsEqualForObjects",
            "IsEqualForMorphisms",
            "IsCongruentForMorphisms",
            ] do
        
        pos := Position( recnames, func );
        if not pos = fail then
            Remove( recnames, pos );
        fi;
        
    od;
    
    create_func_bool :=
      function( name )
        return
          function( arg )
            local eval_arg, result;
            
            eval_arg := ActiveCell( arg );
            
            result := CallFuncList( ValueGlobal( name ), eval_arg );
            
            return result;
            
          end;
          
        end;
    
    create_func_object0 :=
      function( name )
        return
          function( )
            local result;
            
            result := ValueGlobal( name )( C );
            
            return Intrinsify( result );
            
          end;
          
      end;
    
    create_func_object :=
      function( name )
        return
          function( arg )
            local eval_arg, result;
            
            eval_arg := List( arg, ActiveCell );
            
            result := CallFuncList( ValueGlobal( name ), eval_arg );
            
            return Intrinsify( result );
            
          end;
          
      end;
    
    create_func_morphism :=
      function( name )
        local info;
        
        info := CAP_INTERNAL_METHOD_NAME_RECORD.(name);
        
        return
          function( arg )
            local eval_arg, result, src_trg, S, T;
            
            eval_arg := List( arg, ActiveCell );
            
            result := CallFuncList( ValueGlobal( name ), eval_arg );
            
            src_trg := CAP_INTERNAL_GET_CORRESPONDING_OUTPUT_OBJECTS( info.io_type, arg );
            S := src_trg[1];
            T := src_trg[2];
            
            return Intrinsify(
                           result,
                           S,
                           PositionOfActiveCell( S ),
                           T,
                           PositionOfActiveCell( T )
                           );
            
          end;
          
      end;
    
    for name in recnames do
        
        info := CAP_INTERNAL_METHOD_NAME_RECORD.(name);
        
        if info.return_type = "bool" then
            func := create_func_bool( name );
        elif info.return_type = "object" and info.filter_list = [ "category" ] then
            func := create_func_object0( name );
        elif info.return_type = "object" then
            func := create_func_object( name );
        elif info.return_type = "morphism" then
            if not IsBound( info.io_type ) then
                continue;
            elif IsList( info.with_given_without_given_name_pair ) and
              name = info.with_given_without_given_name_pair[1] then
                continue;
            fi;
            func := create_func_morphism( name );
        else
            Error( "unkown return type of the operation ", name );
        fi;
        
        add := ValueGlobal( Concatenation( "Add", name ) );
        
        add( IC, func );
        
    od;
    
    Finalize( IC );
    
    return IC;
    
end );

####################################
#
# View, Print, and Display methods:
#
####################################

##
InstallMethod( ViewObj,
        "for an intrinsic object",
        [ IsIntrinsicObjectRep ],
        
  function( obj )
    
    Print( "<an intrinsic object on active cell: " );
    ViewObj( ActiveCell( obj ) );
    Print( ">" );
    
end );

##
InstallMethod( ViewObj,
        "for an intrinsic morphism",
        [ IsIntrinsicMorphismRep ],
        
  function( mor )
    
    Print( "<an intrinsic morphism on active cell: " );
    ViewObj( ActiveCell( mor ) );
    Print( ">" );
    
end );

##
InstallMethod( Display,
        "for an intrinsic object",
        [ IsIntrinsicObjectRep ],
        
  function( obj )
    
    Display( ActiveCell( obj ) );
    
end );

##
InstallMethod( Display,
        "for an intrinsic morphism",
        [ IsIntrinsicMorphismRep ],
        
  function( mor )
    
    Display( ActiveCell( mor ) );
    
end );
