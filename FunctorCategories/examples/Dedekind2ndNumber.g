#! @Chunk Dedekind2ndNumber

#! The category of presheaves with values in the interval category
#! of the boolean algebra 2^2 has 6 distinct objects.
#! This is the number of distributive lattices generated
#! by a discrete category with two objects.

#! @Example
LoadPackage( "FunctorCategories", false );
#! true
LoadPackage( "Locales", false );
#! true
Q := RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" );
#! Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]
F := FreeCategory( Q );
#! FreeCategory( RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) )
C := F / [ [ F.ab, F.cd ] ];
#! FreeCategory( RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) )
#! / [ a*b = c*d ]
B := PosetOfCategory( C );
#! PosetOfCategory( FreeCategory(
#! RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] )
PSh := PreSheaves( B );
#! PreSheaves( PosetOfCategory( FreeCategory(
#! RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#! IntervalCategory )
Display( PSh );
#! A CAP category with name
#! PreSheaves( PosetOfCategory( FreeCategory(
#! RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#! IntervalCategory ):
#! 
#! 60 primitive operations were used to derive 203 operations for this category
#! which algorithmically
#! * IsEquippedWithHomomorphismStructure
#! * IsCodistributiveCategory
#! * IsDistributiveCategory
#! and furthermore mathematically
#! * IsBicartesianClosedCategory (but not yet algorithmically)
#! * IsBicartesianCoclosedCategory (but not yet algorithmically)
f := PSh.f;
#! <A projective object in PreSheaves( PosetOfCategory( FreeCategory(
#!  RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#!  IntervalCategory )>
A := PSh.A;
#! <A projective object in PreSheaves( PosetOfCategory( FreeCategory(
#!  RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#!  IntervalCategory )>
C := PSh.C;
#! <A projective object in PreSheaves( PosetOfCategory( FreeCategory(
#!  RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#!  IntervalCategory )>
t := PSh.t;
#! <A projective object in PreSheaves( PosetOfCategory( FreeCategory(
#!  RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#!  IntervalCategory )>
IsTerminal( t );
#! true
IsInitial( f );
#! false
List( [ f, A, C, t ], IsReflexive );
#! [ true, true, true, true ]
i := InitialObject( PSh );
#! <An object in PreSheaves( PosetOfCategory( FreeCategory(
#!  RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#!  IntervalCategory )>
IsReflexive( i );
#! false
AC := Coproduct( A, C );
#! <An object in PreSheaves( PosetOfCategory( FreeCategory(
#!  RightQuiver( "Q(f,A,C,t)[a:f->A,b:A->t,c:f->C,d:C->t]" ) ) / [ a*b = c*d ] ),
#!  IntervalCategory )>
IsReflexive( AC );
#! false
#! @EndExample
