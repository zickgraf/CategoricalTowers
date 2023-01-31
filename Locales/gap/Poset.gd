# SPDX-License-Identifier: GPL-2.0-or-later
# Locales: Locales, frames, coframes, meet semi-lattices of locally closed subsets, and Boolean algebras of constructible sets
#
# Declarations
#

#! @Chapter Posets (partially ordered sets)

#! Posets are skeletal, thin categories.

#! @Section Properties

#! @Description
#!  The property of <A>C</A> being a poset (category).
#! @Arguments C
DeclareProperty( "IsPosetCategory",
        IsCapCategory );

AddCategoricalProperty( [ "IsPosetCategory", "IsPosetCategory" ] );

CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsPosetCategory :=
  DuplicateFreeList( Concatenation( [
          "IsEqualForObjectsIfIsHomSetInhabited",
          ],
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsThinCategory ) );

#! @Description
#!  The property of <A>C</A> being a closed monoidal thin skeletal category.
#! @Arguments C
DeclareProperty( "IsMonoidalPoset",
        IsCapCategory );

AddCategoricalProperty( [ "IsMonoidalPoset", "IsMonoidalPoset" ] );

CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsMonoidalPoset :=
  DuplicateFreeList( Concatenation(
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsPosetCategory,
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsMonoidalCategory ) );

#! @Description
#!  The property of <A>C</A> being a closed monoidal thin skeletal category.
#! @Arguments C
DeclareProperty( "IsClosedMonoidalPoset",
        IsCapCategory );

AddCategoricalProperty( [ "IsClosedMonoidalPoset", "IsCoclosedMonoidalPoset" ] );

CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsClosedMonoidalPoset :=
  DuplicateFreeList( Concatenation(
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsMonoidalPoset,
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsClosedMonoidalCategory ) );

#! @Description
#!  The property of <A>C</A> being a coclosed monoidal thin skeletal category.
#! @Arguments C
DeclareProperty( "IsCoclosedMonoidalPoset",
        IsCapCategory );

AddCategoricalProperty( [ "IsCoclosedMonoidalPoset", "IsClosedMonoidalPoset" ] );

CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCoclosedMonoidalPoset :=
  DuplicateFreeList( Concatenation(
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsMonoidalPoset,
          CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCoclosedMonoidalCategory ) );

#! @Section Operations

#! @Description
#!  Check if <A>A</A> is equal to <A>B</A> under the assumption that
#!  there exists a morphism from <A>A</A> to <A>B</A>, i.e., if
#!  <A>A</A> is known to be less or equal to <A>B</A> w.r.t. the partial order.
#! @Arguments A, B
#! @Returns <C>true</C> or <C>false</C>
DeclareOperation( "IsEqualForObjectsIfIsHomSetInhabited",
        [ IsCapCategoryObject, IsCapCategoryObject ] );

# @Section Tools

DeclareGlobalVariable( "POSET_METHOD_NAME_RECORD" );
