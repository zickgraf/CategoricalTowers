# SPDX-License-Identifier: GPL-2.0-or-later
# Locales: Locales, frames, coframes, meet semi-lattices of locally closed subsets, and Boolean algebras of constructible sets
#
# Implementations
#

##
InstallOtherMethod( Visualize,
        "for a datastructure of a constructible object",
        [ IsDatastructureForConstructibleObjects ],
        
  function( C )
    
    if not IsRunningInJupyter( ) then
        TryNextMethod( );
    fi;
    
    Julia.Base.display(
            Julia.Base.MIME( GAPToJulia( "image/svg+xml" ) ),
            GAPToJulia( DotToSVG( DotVertexLabelledDigraph( C ) ) ) );
    
end );
