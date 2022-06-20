# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Implementations
#

##
InstallGlobalFunction( InitialCategory,
  function(  )
    local I;
    
    I := CreateCapCategory( "InitialCategory( )" );

    I!.category_as_first_argument := true;
    
    SetFilterObj( I, IsInitialCapCategory );
    SetFilterObj( I, IsInitialCategory );
    
    SetRangeCategoryOfHomomorphismStructure( I, I );
    
    ##
    AddIsEqualForObjects( I,
      function( I, object1, object2 )
        
        Error( "the initial category `I` has no objects to compare\n" );
        
    end );
    
    ##
    AddIsEqualForMorphisms( I,
      function( I, morphism1, morphism2 )
        
        Error( "the initial category `I` has no morphisms to compare\n" );
        
    end );
    
    ##
    AddIsCongruentForMorphisms( I,
      function( I, morphism1, morphism2 )
        
        Error( "the initial category `I` has no morphisms to compare\n" );
        
    end );
    
    ##
    AddIdentityMorphism( I,
      function( I, object )
        
        Error( "the initial category `I` has no objects\n" );
        
    end );
    
    ##
    AddPreCompose( I,
      function( I, morphism1, morphism2 )
        
        Error( "the initial category `I` has no morphisms to compose\n" );
        
    end );
    
    Finalize( I );
    
    return I;
    
end );
