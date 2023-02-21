#! @BeginChunk CategoryOfQuivers

#! We compute the nerve of the full subcategory of the simplicial category $\Delta$ on the objects $[0], [1], [2]$.

#! @Example
LoadPackage( "FunctorCategories" );
#! true
Delta2 := SimplicialCategoryTruncatedInDegree( 2 );
#! FreeCategory( RightQuiver(
#!   "Delta(C0,C1,C2)[id:C1->C0,s:C0->C1,t:C0->C1,
#!                    is:C2->C1,it:C2->C1,
#!                    ps:C1->C2,pt:C1->C2,mu:C1->C2]" ) ) / relations
Size( Delta2 );
#! 31
N := NerveTruncatedInDegree2( Delta2 );
#! <An object in PreSheaves( FreeCategory(
#!  RightQuiver( "Delta(C0,C1,C2)[id:C1->C0,s:C0->C1,t:C0->C1,
#!  is:C2->C1,it:C2->C1,ps:C1->C2,pt:C1->C2,mu:C1->C2]" ) )
#!  / relations, SkeletalFinSets )>
IsWellDefined( N );
#! true
PSh := CapCategory( N );
#! PreSheaves( FreeCategory( RightQuiver(
#!   "Delta(C0,C1,C2)[id:C1->C0,s:C0->C1,t:C0->C1,is:C2->C1,it:C2->C1,
#!                    ps:C1->C2,pt:C1->C2,mu:C1->C2]" ) ) / relations,
#! SkeletalFinSets )
QuiversOverDelta2 := CategoryOfQuivers( Delta2 );
#! CategoryOfQuivers( FreeCategory(
#! RightQuiver( "Delta(C0,C1,C2)[id:C1->C0,s:C0->C1,t:C0->C1,
#! is:C2->C1,it:C2->C1,ps:C1->C2,pt:C1->C2,mu:C1->C2]" ) ) / relations )
datum0 := CoYonedaLemmaOnObjects( PSh.C0 );
#! [ [ <(C0)>, <(C1)>, <(C2)> ],
#!   [ [ 1, (C1)-[(id)]->(C0), 0 ], [ 0, (C0)-[(s)]->(C1), 1 ],
#!     [ 0, (C0)-[(t)]->(C1), 1 ], [ 2, (C2)-[(is)]->(C1), 1 ],
#!     [ 2, (C2)-[(it)]->(C1), 1 ], [ 1, (C1)-[(ps)]->(C2), 2 ],
#!     [ 1, (C1)-[(pt)]->(C2), 2 ], [ 1, (C1)-[(mu)]->(C2), 2 ] ] ]
q := CreateQuiverInCategory( QuiversOverDelta2, datum0 );
#! <An object in CategoryOfQuivers( FreeCategory(
#!  RightQuiver( "Delta(C0,C1,C2)[id:C1->C0,s:C0->C1,t:C0->C1,
#!  is:C2->C1,it:C2->C1,ps:C1->C2,pt:C1->C2,mu:C1->C2]" ) ) / relations )>
IsWellDefined( q );
#! true
#! @EndExample
#! @EndChunk