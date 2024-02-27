/**
  @file 

  @ingroup cudd

  @brief Functions for manipulating 3-valued BDDs.

  @author Matej Pavlik
*/

#include "cuddInt.h"
#include <assert.h>

static void clearMaxrefFlagRecur(DdNode *f);
static void countNodeScore(DdManager *dd, DdNode *f, unsigned int *con, unsigned int *score);

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


DdNode *
Cudd_BddReduceByNodeLimit(
  DdManager *dd,
  DdNode *f,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    unsigned int consumed = 0, reduced = 0;
    DdNode *res = cuddBddReduceByNodeLimitRecur(dd, f, h, limit, &consumed, &reduced);
    clearMaxrefFlagRecur(res);
    return(res);
}


static void clearMaxrefFlagRecur(DdNode *f) {
  DdNode *F = Cudd_Regular(f);
  if (F == NULL || Cudd_IsConstant(F) || !DD_MAXREF_IS_FLAG_SET(F->ref)) {
    return;
  }
  DD_MAXREF_CLEAR_FLAG(F->ref);
  clearMaxrefFlagRecur(cuddT(F));
  clearMaxrefFlagRecur(cuddE(F));
}


int randomTraverse(DdManager *dd, DdNode *f, DdNode *g, DdNode *h)
{
  UNUSED(f);
  UNUSED(g);
  UNUSED(h);
  return (Cudd_Random(dd) % 2) ? -1 : 1;
}


#define DD_GET_NODE_INDEX(x) (((x) == unknown) ? INT_MAX : dd->perm[(x)->index])


/**
  @brief Chooses next step in a tree traversal. At least one of the nodes must be
  non-constant.

  @return negative number if then-branch is chosen; non-negative number if
  else-branch is chosen

  @sideeffect None

*/
int greedyTraverseOneStep(DdManager *dd, DdNode *f, DdNode *g, DdNode *h)
{
  DdNode *unknown = DD_UNKNOWN(dd);
  DdNode *F = Cudd_Regular(f), *G, *H;
  unsigned int index, tscore = 0, escore = 0, tconst = 0, econst = 0, findex, gindex = 0, hindex = 0;
  DdNode *t, *e;
  
  findex = DD_GET_NODE_INDEX(F);
  index = findex;
  
  if (g != NULL) {
    G = Cudd_Regular(g);
    gindex = DD_GET_NODE_INDEX(G);
    index = ddMin(index, gindex);
  }
  
  if (h != NULL) {
    H = Cudd_Regular(h);
    hindex = DD_GET_NODE_INDEX(H);
    index = ddMin(index, hindex);
  }
  
  if (findex == index) {
    t = cuddT(F), e = Cudd_Regular(cuddE(F));
    
    if (Cudd_IsConstant(t)) tconst += 1;
    else                    tscore += dd->perm[t->index];
    
    if (Cudd_IsConstant(e)) econst += 1;
    else                    escore += dd->perm[e->index];
  }
  
  if (g != NULL && gindex == index) {
    t = cuddT(G), e = Cudd_Regular(cuddE(G));
    
    if (Cudd_IsConstant(t)) tconst += 1;
    else                    tscore += dd->perm[t->index];
    
    if (Cudd_IsConstant(e)) econst += 1;
    else                    escore += dd->perm[e->index];
  }
  
  
  if (h != NULL && hindex == index) {
    t = cuddT(H), e = Cudd_Regular(cuddE(H));
    
    if (Cudd_IsConstant(t)) tconst += 1;
    else                    tscore += dd->perm[t->index];
    
    if (Cudd_IsConstant(e)) econst += 1;
    else                    escore += dd->perm[e->index];
  }

  return (tconst > econst || (tconst == econst && tscore > escore)) ? -1
       : (tconst < econst || (tconst == econst && tscore < escore)) ? 1
       : (Cudd_Random(dd) % 2) ? -1 : 1;
}


static void countNodeScore(DdManager *dd, DdNode *f, unsigned int *con, unsigned int *score)
{
  /*f = Cudd_Regular(f);
  if (f == DD_ONE(dd))          *con += 1;
  else if (!Cudd_IsConstant(f)) *score += dd->perm[f->index];*/
  
  
  f = Cudd_Regular(f);
  if (Cudd_IsConstant(f)) *con += 1;
  else                    *score += dd->perm[f->index];
}


/**
  @brief Chooses next step in a tree traversal. At least one of the nodes must be
  non-constant.

  @return negative number if then-branch is chosen; non-negative number if
  else-branch is chosen

  @sideeffect None

*/
int greedyTraverseTwoStep(DdManager *dd, DdNode *f, DdNode *g, DdNode *h)
{
  DdNode *unknown = DD_UNKNOWN(dd);
  DdNode *F = Cudd_Regular(f), *G, *H;
  unsigned int index, tscore = 0, escore = 0, tconst = 0, econst = 0, findex, gindex = 0, hindex = 0;
  DdNode *t, *e;
  
  findex = DD_GET_NODE_INDEX(F);
  index = findex;
  
  if (g != NULL) {
    G = Cudd_Regular(g);
    gindex = DD_GET_NODE_INDEX(G);
    index = ddMin(index, gindex);
  }
  
  if (h != NULL) {
    H = Cudd_Regular(h);
    hindex = DD_GET_NODE_INDEX(H);
    index = ddMin(index, hindex);
  }
  
  if (findex == index) {
    t = cuddT(F), e = Cudd_Regular(cuddE(F));
    
    if (Cudd_IsConstant(t)) tconst += 8;
    else {
      countNodeScore(dd, cuddT(t), &tconst, &tscore);
      countNodeScore(dd, cuddE(t), &tconst, &tscore);
    }
    
    if (Cudd_IsConstant(e)) econst += 8;
    else {
      countNodeScore(dd, cuddT(e), &econst, &escore);
      countNodeScore(dd, cuddE(e), &econst, &escore);
    }
  }
  
  if (g != NULL && gindex == index) {
    t = cuddT(G), e = Cudd_Regular(cuddE(G));
    
    if (Cudd_IsConstant(t)) tconst += 8;
    else {
      countNodeScore(dd, cuddT(t), &tconst, &tscore);
      countNodeScore(dd, cuddE(t), &tconst, &tscore);
    }
    
    if (Cudd_IsConstant(e)) econst += 8;
    else {
      countNodeScore(dd, cuddT(e), &econst, &escore);
      countNodeScore(dd, cuddE(e), &econst, &escore);
    }
  }
  
  
  if (h != NULL && hindex == index) {
    t = cuddT(H), e = Cudd_Regular(cuddE(H));
    
    if (Cudd_IsConstant(t)) tconst += 8;
    else {
      countNodeScore(dd, cuddT(t), &tconst, &tscore);
      countNodeScore(dd, cuddE(t), &tconst, &tscore);
    }
    
    if (Cudd_IsConstant(e)) econst += 8;
    else {
      countNodeScore(dd, cuddT(e), &econst, &escore);
      countNodeScore(dd, cuddE(e), &econst, &escore);
    }
  }

  return (tconst > econst || (tconst == econst && tscore > escore)) ? -1
       : (tconst < econst || (tconst == econst && tscore < escore)) ? 1
       : (Cudd_Random(dd) % 2) ? -1 : 1;
}


DdNode *
cuddBddReduceByNodeLimitRecur(
  DdManager *dd,
  DdNode *f,
  DD_TRAV_HEU h,
  unsigned int limit,
  unsigned int * nodesConsumed,
  unsigned int * resultReduced)
{
  DdNode *one = DD_ONE(dd);
  DdNode *zero = Cudd_Not(one);
  DdNode *unknown = DD_UNKNOWN(dd);
  DdNode *F, *t, *e, *bt, *be, *r;
  
  if (f == one || f == zero || f == unknown) {
    return(f);
  }

  /* bdd is not constant now */
  
  F = Cudd_Regular(f);
  
  /* Check if the node is already included in the DD. */
  if (DD_MAXREF_IS_FLAG_SET(F->ref)) { 
    return(f);
  }
  
  if (limit <= 0) {
    *resultReduced = 1;
    return(unknown);
  }
  
  bt = Cudd_NotCond(cuddT(F), F != f && cuddT(F) != unknown);
  be = Cudd_NotCond(cuddE(F), F != f && cuddE(F) != unknown);
    
  int decision = h(dd, f, NULL, NULL);
  unsigned int consumed = 0;
  unsigned int reduced = 0;
  
  if (decision < 0) { // then branch first
    t = cuddBddReduceByNodeLimitRecur(dd, bt, h, limit - 1, &consumed, &reduced);
    if (t == NULL) { return (NULL); }
    cuddRef(t);
    *nodesConsumed += consumed;
    
    consumed = 0;
    e = cuddBddReduceByNodeLimitRecur(dd, be, h, limit - 1 - *nodesConsumed, &consumed, &reduced);
    if (e == NULL) {
      Cudd_IterDerefBdd(dd, t);
      return (NULL);
    }
    cuddRef(e);
    *nodesConsumed += consumed;
    *resultReduced |= reduced;
  } else { // else branch first
    consumed = 0;
    e = cuddBddReduceByNodeLimitRecur(dd, be, h, limit - 1, &consumed, &reduced);
    if (e == NULL) { return (NULL); }
    cuddRef(e);
    *nodesConsumed += consumed;
    
    consumed = 0;
    t = cuddBddReduceByNodeLimitRecur(dd, bt, h, limit - 1 - *nodesConsumed, &consumed, &reduced);
    if (t == NULL) {
      Cudd_IterDerefBdd(dd, e);
      return (NULL);
    }
    cuddRef(t);
    *nodesConsumed += consumed;
    *resultReduced |= reduced;
  }

  if (t == e) {
    r = t;
  } else {
    int complementRes = 0;
    if (Cudd_IsComplement(t)) {
      r = cuddUniqueInter(dd, (int) F->index, Cudd_Not(t), Cudd_NotCond(e, e != unknown));
      complementRes = 1;
    } else  if (t == unknown && Cudd_IsComplement(e)) { /* Maintain canonical form. */
      r = cuddUniqueInter(dd, (int) F->index, t, Cudd_Not(e));
      complementRes = 1;
    } else {
      r = cuddUniqueInter(dd, (int) F->index, t, e);
    }
    if (r == NULL) {
      Cudd_IterDerefBdd(dd, t);
      Cudd_IterDerefBdd(dd, e);
      return (NULL);
    }
    
    if (!DD_MAXREF_IS_FLAG_SET(r->ref)) {
      DD_MAXREF_SET_FLAG(r->ref);
      *nodesConsumed += 1;
    }
    
    if (complementRes) {
      r = Cudd_Not(r);
    }
  }
  
  cuddDeref(e);
  cuddDeref(t);
  return (r);
} /* end of cuddBddReduceByNodeLimitRecur */


