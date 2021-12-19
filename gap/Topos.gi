# SPDX-License-Identifier: GPL-2.0-or-later
# Toposes: Elementary toposes
#
# Implementations
#

InstallTrueMethod( IsCartesianClosedCategory, IsElementaryTopos );
InstallTrueMethod( IsCocartesianCategory, IsElementaryTopos );

##
InstallOtherMethod( DirectProductOp,
        [ IsCapCategory, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( cat, object_1, object_2 )
    
    return DirectProductOp( cat, [ object_1, object_2 ] );
    
end );

##
InstallMethod( CoproductOp,
        [ IsCapCategory, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( cat, object_1, object_2 )
    
    return Coproduct( cat, [ object_1, object_2 ] );
    
end );
