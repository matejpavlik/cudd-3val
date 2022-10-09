/**
  @file 

  @ingroup cudd

  @brief Functions for manipulating 3-valued BDDs.

  @author Matej Pavlik
*/

#include "cuddInt.h"
#include <assert.h>

/**
  @brief The valuations leading to 0 lead to 'unknown' in the resulting diagram.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

*/
DdNode *
Cudd_BddForgetZeros(
        DdManager * dd,
        DdNode * f)
{
    DdNode *result = Cudd_bddOr(dd,f , DD_UNKNOWN(dd));
    return(result);
}

/**
  @brief The valuations leading to 1 lead to 'unknown' in the resulting diagram.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

*/
DdNode *
Cudd_BddForgetOnes(
        DdManager * dd,
        DdNode * f)
{
    DdNode *result = Cudd_bddAnd(dd, f, DD_UNKNOWN(dd));
    return(result);
}

/**
  @brief Merges under- and overapproximating BDDs into a single BDD.

  @return a pointer to the resulting %BDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

*/
DdNode *
Cudd_BddMergeInterval(
        DdManager * dd,
        DdNode * under,
        DdNode * over)
{
    DdNode *tmp = Cudd_bddOr(dd, under, DD_UNKNOWN(dd));
    Cudd_Ref(tmp);
    DdNode *result = Cudd_bddAnd(dd, tmp, over);
    Cudd_RecursiveDeref(dd, tmp);
    return(result);
}


DdNode *
Cudd_BddReduceByValuation(
  DdManager *dd,
  DdNode *bdd,
  DdNode *val)
{
  DdNode *one = DD_ONE(dd);
  DdNode *zero = Cudd_Not(one);
  DdNode *unknown = DD_UNKNOWN(dd);
  DdNode *B, *V, *t, *e, *T, *E, *bt, *be, *vt, *ve, *r;
  int topb, topv, index;

  if (bdd == one || bdd == zero || bdd == unknown)
    return(bdd);

  if (val == one)
    return(bdd);

  if (val == zero)
    return(unknown);

  /* bdd, val are not constant now */
  
  B = Cudd_Regular(bdd);
  V = Cudd_Regular(val);

  topb = dd->perm[B->index];
  topv = dd->perm[V->index];
  index = ddMin(topb, topv);
    
  if (topb > topv && Cudd_bddIsVar(dd, V)) {
    return(bdd);
  }

  if (topb <= topv) {
    bt = Cudd_NotCond(cuddT(B), B != bdd && cuddT(B) != unknown);
    be = Cudd_NotCond(cuddE(B), B != bdd && cuddE(B) != unknown);
  } else {
    bt = be = bdd;
  }
  
  if (topb >= topv) {
    vt = Cudd_NotCond(cuddT(V), V != val && cuddT(V) != unknown);
    ve = Cudd_NotCond(cuddE(V), V != val && cuddE(V) != unknown);
  } else {
    vt = ve = val;
  }
  
  T = Cudd_Regular(t = Cudd_BddReduceByValuation(dd, bt, vt));
  E = Cudd_Regular(e = Cudd_BddReduceByValuation(dd, be, ve));

  r = (t == e) ? t : NULL;

  if (topb < topv && Cudd_bddIsVar(dd, V)) {
    /* == on the run forgetting == */
    if (!Cudd_IsComplement(val)) {
      if (V->index == T->index) { /* no need for non-constant testing */
        if ((t == T && cuddT(T) == e)
            || (t != T && cuddT(T) == Cudd_Not(e))) {
          t = e;
          e = unknown;
          index = V->index;
        }
      } else if (V->index == E->index) {
        if ((e == E && cuddT(E) == t)
            || (e != E && cuddT(E) == Cudd_Not(t))) {
          e = unknown;
          index = V->index;
        }
      }
    } else /* Cudd_IsComplement(val)*/ {
      if (V->index == T->index) { /* no need for non-constant testing */
        if ((t == T && cuddE(T) == e)
            || (t != T && cuddE(T) == Cudd_Not(e))) {
          t = unknown;
          index = V->index;
        }
      } else if (V->index == E->index) {
        if ((e == E && cuddE(E) == t)
              || (e != E && cuddE(E) == Cudd_Not(t))) {
          e = t;
          t = unknown;
          index = V->index;
        }
      }
    }
  }
  
  if (r == NULL) {
    if (Cudd_IsComplement(t)) {
      r = Cudd_Not(cuddUniqueInter(dd, index, Cudd_Regular(t), Cudd_NotCond(e,e!=unknown)));
    } else if (t == unknown && Cudd_IsComplement(e)) {
      r = Cudd_Not(cuddUniqueInter(dd, index, t, Cudd_Not(e)));
    } else {
      r = cuddUniqueInter(dd, index, t, e);
    }
  }

  return(r);
}
