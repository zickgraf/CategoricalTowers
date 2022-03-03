##  L <-l-- K --r-> R
##  |       |       |
##  |       |       |
##  m   1   n   2   p
##  |       |       |
##  v       v       V
##  G <-g-- D --h-> H

LoadPackage( "FunctorCategories" );

## Construct the category of directed graphs as the functor category from
## the (free category generated by the) graphs quiver to the category of finite sets

quivers_quiver := RightQuiver( "q(V,A)[s:V->A,t:V->A]" );
F := FreeCategory( quivers_quiver );

N := NerveTruncatedInDegree2( F );
Assert( 0, IsWellDefined( N ) );

Quivers := PreSheaves( F, FinSets );
Fop := Source( Quivers );
Y := YonedaEmbedding( F );

Display( Y( F.V ) );
Display( Y( F.A ) );

D := DistinguishedObjectOfHomomorphismStructure( Fop );

ss := MapOfFinSets( D, [ 1 ], HomStructure( Fop.A, Fop.V ) );
tt := MapOfFinSets( D, [ 2 ], HomStructure( Fop.A, Fop.V ) );

s := InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( Fop, Fop.A, Fop.V, ss );
t := InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( Fop, Fop.A, Fop.V, tt );

Assert( 0, InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( s ) = ss );
Assert( 0, InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( t ) = tt );

## The rewriting rule
K_V := FinSet( [ 1, 2 ] );
K_A := InitialObject( FinSets );
K := AsObjectInFunctorCategory( Fop,
             rec( A := K_A, V := K_V ),
             rec( s := UniversalMorphismFromInitialObject( K_V ),
                  t := UniversalMorphismFromInitialObject( K_V ) ) );
Assert( 0, IsWellDefined( K ) );

L_V := FinSet( [ 1, 2, 4 ] );
L_A := FinSet( [ "2A1", "4A1", "4A4" ] );
L := AsObjectInFunctorCategory( Fop,
             rec( A := L_A, V := L_V ),
             rec( s := MapOfFinSets( L_A, [ [ "2A1", 2 ], [ "4A1", 4 ], [ "4A4", 4 ] ], L_V ),
                  t := MapOfFinSets( L_A, [ [ "2A1", 1 ], [ "4A1", 1 ], [ "4A4", 4 ] ], L_V ) ) );
Assert( 0, IsWellDefined( L ) );

D_V := FinSet( [ 1, 2, 3 ] );
D_A := FinSet( [ "3A1", "3A2" ] );
D := AsObjectInFunctorCategory( Fop,
             rec( A := D_A, V := D_V ),
             rec( s := MapOfFinSets( D_A, [ [ "3A1", 3 ], [ "3A2", 3 ] ], D_V ),
                  t := MapOfFinSets( D_A, [ [ "3A1", 1 ], [ "3A2", 2 ] ], D_V ) ) );
Assert( 0, IsWellDefined( D ) );

R_V := FinSet( [ 1, 2, 3 ] );
R_A := FinSet( [ "3A1", "1A2" ] );
R := AsObjectInFunctorCategory( Fop,
             rec( A := R_A, V := R_V ),
             rec( s := MapOfFinSets( R_A, [ [ "3A1", 3 ], [ "1A2", 1 ] ], R_V ),
                  t := MapOfFinSets( R_A, [ [ "3A1", 1 ], [ "1A2", 2 ] ], R_V ) ) );
Assert( 0, IsWellDefined( R ) );

l := AsMorphismInFunctorCategory(
             K,
             rec( A := EmbeddingOfFinSets( K_A, L_A ),
                  V := EmbeddingOfFinSets( K_V, L_V ) ),
             L );
Assert( 0, IsWellDefined( l ) );

r := AsMorphismInFunctorCategory(
             K,
             rec( A := EmbeddingOfFinSets( K_A, R_A ),
                  V := EmbeddingOfFinSets( K_V, R_V ) ),
             R );
Assert( 0, IsWellDefined( r ) );

n := AsMorphismInFunctorCategory(
             K,
             rec( A := EmbeddingOfFinSets( K_A, D_A ),
                  V := EmbeddingOfFinSets( K_V, D_V ) ),
             D );
Assert( 0, IsWellDefined( n ) );

## The matching
G_V := FinSet( [ 1 .. 4 ] );
G_A := FinSet( [ "2A1", "4A1", "4A4", "3A1", "3A2" ] );
G := AsObjectInFunctorCategory( Fop,
             rec( A := G_A, V := G_V ),
             rec( s := MapOfFinSets( G_A, [ [ "2A1", 2 ], [ "4A1", 4 ], [ "4A4", 4 ], [ "3A1", 3 ], [ "3A2", 3 ] ], G_V ),
                  t := MapOfFinSets( G_A, [ [ "2A1", 1 ], [ "4A1", 1 ], [ "4A4", 4 ], [ "3A1", 1 ], [ "3A2", 2 ] ], G_V ) ) );
Assert( 0, IsWellDefined( G ) );

m := AsMorphismInFunctorCategory(
             L,
             rec( A := EmbeddingOfFinSets( L_A, G_A ),
                  V := EmbeddingOfFinSets( L_V, G_V ) ),
             G );
Assert( 0, IsWellDefined( m ) );

H := Pushout( n, r );
h := InjectionOfCofactorOfPushoutWithGivenPushout( [ n, r ], 1, H );
p := InjectionOfCofactorOfPushoutWithGivenPushout( [ n, r ], 2, H );
