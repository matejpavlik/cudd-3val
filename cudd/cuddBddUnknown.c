/**
  @file 

  @ingroup cudd

  @brief Functions for manipulating 3-valued BDDs.

  @author Matej Pavlik
*/

#include "util.h"
#include "cuddInt.h"
#include <assert.h>

#define DD_MIN_NODE_LIMIT(x) ((x) < 1 ? 0 : (x) - 1)

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


DdNode *
Cudd_bddIteReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DdNode * i /**< third operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res;
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddIteReducedRecur(dd,f,g,i,h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);
} /* end of Cudd_bddIteReduced */


DdNode *
Cudd_bddAndReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res;
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddAndReducedRecur(dd,f,g,h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);
} /* end of Cudd_bddAndReduced */


DdNode *
Cudd_bddOrReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res, *unknown;
    unknown = DD_UNKNOWN(dd);
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddAndReducedRecur(dd,Cudd_NotCond(f,f != unknown), Cudd_NotCond(g,g != unknown),h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    res = Cudd_NotCond(res,res != NULL && res != unknown);
    return(res);
} /* end of Cudd_bddOrReduced */


DdNode *
Cudd_bddNandReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res, *unknown;
    unknown = DD_UNKNOWN(dd);
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddAndReducedRecur(dd,f,g,h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    res = Cudd_NotCond(res,res != NULL && res != unknown);
    return(res);
} /* end of Cudd_bddNandReduced */


DdNode *
Cudd_bddNorReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res, *unknown;
    unknown = DD_UNKNOWN(dd);
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddAndReducedRecur(dd,Cudd_NotCond(f,f != unknown),Cudd_NotCond(g,g != unknown),h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);
} /* end of Cudd_bddNorReduced */


DdNode *
Cudd_bddXorReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res;
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddXorReducedRecur(dd,f,g,h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    return(res);
} /* end of Cudd_bddXorReduced */


DdNode *
Cudd_bddXnorReduced(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DD_TRAV_HEU h,
  unsigned int limit)
{
    DdNode *res, *unknown;
    unknown = DD_UNKNOWN(dd);
    do {
	dd->reordered = 0;
	unsigned int consumed = 0, reduced = 0;
	res = cuddBddXorReducedRecur(dd,f,g,h,limit,&consumed, &reduced);
        clearMaxrefFlagRecur(res);
    } while (dd->reordered == 1);
    if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
        dd->timeoutHandler(dd, dd->tohArg);
    }
    res = Cudd_NotCond(res,res != NULL && res != unknown);
    return(res);
} /* end of Cudd_bddXnorReduced */


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


DdNode *
cuddBddIteReducedRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h,
  DD_TRAV_HEU heu,
  unsigned int limit,
  unsigned int * nodesConsumed,
  unsigned int * resultReduced)
{
    DdNode	 *one, *zero, *unknown, *res;
    DdNode	 *r, *Fv, *Fnv, *Gv, *Gnv, *H, *Hv, *Hnv, *t, *e;
    int		 topf, topg, toph, v;
    unsigned int index;
    int comple;
    unsigned int consumed, reduced;
    
    statLine(dd);
    one = DD_ONE(dd);
    zero = Cudd_Not(one);
    unknown = DD_UNKNOWN(dd);
    consumed = 0, reduced = 0;

    /* Terminal cases. */

    /* One variable cases. */
    if (f == one || g == h) {	/* ITE(1,G,H) = ITE(F,G,G) = G */
        r = cuddBddReduceByNodeLimitRecur(dd, g, heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return r;
    }

    if (f == zero) {	/* ITE(0,G,H) = H */
        r = cuddBddReduceByNodeLimitRecur(dd, h, heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return r;
    }

    if ((((f == unknown) + (g == unknown) + (h == unknown)) >= 2)
        || (f == unknown && g == Cudd_NotCond(h,h != unknown)))
        return(unknown);

    if (f == unknown) {
        return(unknown);
    }

    /* From now on, f is known not to be a constant. */
    if (g == one || f == g) {	/* ITE(F,F,H) = ITE(F,1,H) = F + H */
        if (h == zero) {	/* ITE(F,F,0) = ITE(F,1,0) = F */
            return(f);
        } else {
            res = cuddBddAndReducedRecur(dd,Cudd_NotCond(f,f != unknown),Cudd_NotCond(h,h != unknown), heu, limit, &consumed, &reduced);
            *nodesConsumed += consumed;
            *resultReduced |= reduced;
            return(Cudd_NotCond(res,res != NULL && res != unknown));
        }
    } else if (g == zero) { /* ITE(F,0,H) = !F * H */
        if (h == one) {		/* ITE(F,0,1) = !F */
            return(Cudd_Not(f));
        } else {
            res = cuddBddAndReducedRecur(dd,Cudd_NotCond(f,f != unknown),h, heu, limit, &consumed, &reduced);
            *nodesConsumed += consumed;
            *resultReduced |= reduced;
            return(res);
        }
    }
    if (h == zero) {    /*  ITE(F,G,0) = F * G */
        res = cuddBddAndReducedRecur(dd,f,g, heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return(res);
    } else if (h == one) { /* ITE(F,G,1) = !F + G */
        res = cuddBddAndReducedRecur(dd,f,Cudd_NotCond(g, g != unknown), heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return(Cudd_NotCond(res,res != NULL && res != unknown));
    }

    /* Check remaining cases. */
    if (g == Cudd_Not(h)) { /* ITE(F,G,!G) = F <-> G */
        res = cuddBddXorReducedRecur(dd,f,h, heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return(res);
    } else if (g == unknown || h == unknown) {
        return unknown;
    }
    
    /* From here, there are no constants. */
    comple = bddVarToCanonicalSimple(dd, &f, &g, &h, &topf, &topg, &toph);

    /* f & g are now regular pointers */

    v = ddMin(topg, toph);

    /* A shortcut: ITE(F,G,H) = (v,G,H) if F = (v,1,0), v < top(G,H). */
    if (topf < v && cuddT(f) == one && cuddE(f) == zero) {
        r = cuddUniqueInter(dd, (int) f->index, g, h);
        if (r == NULL) {
          return(NULL);
        }
        
        if (!DD_MAXREF_IS_FLAG_SET(r->ref)) {
          if (limit == 0) {
            cuddRef(r);
            Cudd_IterDerefBdd(dd, r);
            *resultReduced = 1;
            return(unknown);
          }
          DD_MAXREF_SET_FLAG(r->ref);
          *nodesConsumed += 1;
        }
        return(Cudd_NotCond(r,comple && r != unknown && r != NULL));
    }

    /* Check cache. */
    // Suppress cache in reduced algorithms
    r = cuddCacheLookup(dd, DD_BDD_ITE_TAG, f, g, h);
    if (r != NULL) {
        cuddRef(r);
        DdNode *res = cuddBddReduceByNodeLimitRecur(dd, r, heu, limit, &consumed, &reduced);
        cuddRef(res);
        Cudd_IterDerefBdd(dd, r);
        cuddDeref(res);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return(Cudd_NotCond(res,comple && res != unknown));
    }

    checkWhetherToGiveUp(dd);

    /* Compute cofactors. */
    index = f->index;
    if (topf <= v) {
        v = ddMin(topf, v);	/* v = top_var(F,G,H) */
        Fv = cuddT(f); Fnv = cuddE(f);
    } else {
        Fv = Fnv = f;
    }
    if (topg == v) {
        index = g->index;
        Gv = cuddT(g); Gnv = cuddE(g);
    } else {
        Gv = Gnv = g;
    }
    if (toph == v) {
        H = Cudd_Regular(h);
        #ifdef DD_DEBUG
        assert(cuddE(H) != Cudd_Not(unknown));
        #endif
        index = H->index;
        Hv = cuddT(H); Hnv = cuddE(H);
        if (Cudd_IsComplement(h)) {
            Hv = Cudd_NotCond(Hv,Hv != unknown);
            Hnv = Cudd_NotCond(Hnv,Hnv != unknown);
        }
    } else {
        Hv = Hnv = h;
    }
    
    int decision = heu(dd, f, g, h);
    
    /* Recursive step. */
    if (decision < 0) { // then branch first
        t = cuddBddIteReducedRecur(dd, Fv, Gv, Hv, heu, DD_MIN_NODE_LIMIT(limit), &consumed, &reduced);
        if (t == NULL) { return(NULL); }
        cuddRef(t);
        *nodesConsumed += consumed;
    
        consumed = 0;
        e = cuddBddIteReducedRecur(dd, Fnv, Gnv, Hnv, heu, DD_MIN_NODE_LIMIT(limit - *nodesConsumed), &consumed, &reduced);
        if (e == NULL) {
            Cudd_IterDerefBdd(dd, t);
            return(NULL);
        }
        cuddRef(e);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
    } else {
        e = cuddBddIteReducedRecur(dd, Fnv, Gnv, Hnv, heu, DD_MIN_NODE_LIMIT(limit), &consumed, &reduced);
        if (e == NULL) { return(NULL); }
        cuddRef(e);
        *nodesConsumed += consumed;
    
        consumed = 0;
        t = cuddBddIteReducedRecur(dd, Fv, Gv, Hv, heu, DD_MIN_NODE_LIMIT(limit - *nodesConsumed), &consumed, &reduced);
        if (t == NULL) {
            Cudd_IterDerefBdd(dd, e);
            return(NULL);
        }
        cuddRef(t);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
    }
    
    if (t == e) {
        r = t;
    } else {
        if (Cudd_IsComplement(t)) {
            comple = !comple;
            t = Cudd_Not(t);
            e = Cudd_NotCond(e, e != unknown);
        } else if (t == unknown && Cudd_Not(e) == Cudd_Regular(e)) {
            comple = !comple;
            e = Cudd_Regular(e);
        }
        r = cuddUniqueInter(dd,index,t,e);
        
        if (r == NULL) {
            Cudd_IterDerefBdd(dd,t);
            Cudd_IterDerefBdd(dd,e);
            return(NULL);
        }
        
        if (!DD_MAXREF_IS_FLAG_SET(r->ref)) {
          if (limit == 0) {
            cuddDeref(e);
            cuddDeref(t);
            cuddRef(r);
            Cudd_IterDerefBdd(dd, r);
            *resultReduced = 1;
            return(unknown);
          }
          DD_MAXREF_SET_FLAG(r->ref);
          *nodesConsumed += 1;
        }
    }
    
    cuddDeref(t);
    cuddDeref(e);
    
    if (!*resultReduced) {
        cuddCacheInsert(dd, DD_BDD_ITE_TAG, f, g, h, r);
    }
    return(Cudd_NotCond(r,comple && r != unknown));
}  /* end of cuddBddIteReducedRecur */



DdNode *
cuddBddAndReducedRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * g,
  DD_TRAV_HEU heu,
  unsigned int limit,
  unsigned int * nodesConsumed,
  unsigned int * resultReduced) {
    DdNode *F, *fv, *fnv, *G, *gv, *gnv;
    DdNode *one, *unknown, *r, *t, *e;
    int topf, topg;
    unsigned int index;
    unsigned int consumed, reduced;
    
    statLine(manager);
    one = DD_ONE(manager);
    unknown = DD_UNKNOWN(manager);
    consumed = 0, reduced = 0;

    /* Terminal cases. */
    F = Cudd_Regular(f);
    G = Cudd_Regular(g);
    if (F == G) {
        if (f == g) {
            r = cuddBddReduceByNodeLimitRecur(manager, f, heu, limit, &consumed, &reduced);
            *nodesConsumed += consumed;
            *resultReduced |= reduced;
            return r;
        }
        else if (F == unknown) { 
            return (unknown);
        }
    }
    if (F == one) {
        if (f == one) {
            r = cuddBddReduceByNodeLimitRecur(manager, g, heu, limit, &consumed, &reduced);
            *nodesConsumed += consumed;
            *resultReduced |= reduced;
            return r;
        }
        else { 
            return (f);
        }
    }
    if (G == one) {
        if (g == one) {
            r = cuddBddReduceByNodeLimitRecur(manager, f, heu, limit, &consumed, &reduced);
            *nodesConsumed += consumed;
            *resultReduced |= reduced;
            return r;
        }
        else { 
            return (g);
        }
    }
    
    /* At this point f and g are not constant or at most one of f, g is constant unknown. */
    if (f > g) { /* Try to increase cache efficiency. */
        DdNode *tmp = f;
        f = g;
        g = tmp;
        F = Cudd_Regular(f);
        G = Cudd_Regular(g);
    }

    /* Check cache. */
    // Suppress cache in reduced algorithms
    if (F->ref != 1 || G->ref != 1) {
        r = cuddCacheLookup2(manager, Cudd_bddAnd, f, g);
        if (r != NULL) {
            cuddRef(r);
            DdNode *res = cuddBddReduceByNodeLimitRecur(manager, r, heu, limit, &consumed, &reduced);
            if (res != NULL) {
                cuddRef(res);
                Cudd_IterDerefBdd(manager, r);
                cuddDeref(res);
                *nodesConsumed += consumed;
                *resultReduced |= reduced;
            } else {
                Cudd_IterDerefBdd(manager, r);
            }
            return  res;
        }
    }

    checkWhetherToGiveUp(manager);

    /* Here we can skip the use of cuddI, because the operands are known
    ** to be non-constant.
    */
    if (F == unknown) {
        topf = INT_MAX;
    } else {
        topf = manager->perm[F->index];
    }
    if (G == unknown) {
        topg = INT_MAX;
    } else {
        topg = manager->perm[G->index];
    }

    /* Compute cofactors. */
    if (topf <= topg) {
        index = F->index;
        fv = cuddT(F);
        fnv = cuddE(F);
        if (Cudd_IsComplement(f)) {
            fv = Cudd_NotCond(fv, fv != unknown);
            fnv = Cudd_NotCond(fnv, fnv != unknown);
        }
    } else {
        index = G->index;
        fv = fnv = f;
    }

    if (topg <= topf) {
        gv = cuddT(G);
        gnv = cuddE(G);
        if (Cudd_IsComplement(g)) {
            gv = Cudd_NotCond(gv, gv != unknown);
            gnv = Cudd_NotCond(gnv, gnv != unknown);
        }
    } else {
        gv = gnv = g;
    }
    
    int decision = heu(manager, f, g, NULL);
    
    if (decision < 0) { // then branch first
        t = cuddBddAndReducedRecur(manager, fv, gv, heu, DD_MIN_NODE_LIMIT(limit), &consumed, &reduced);
        if (t == NULL) { return (NULL); }
        cuddRef(t);
        *nodesConsumed += consumed;
        
        consumed = 0;
        e = cuddBddAndReducedRecur(manager, fnv, gnv, heu, DD_MIN_NODE_LIMIT(limit - *nodesConsumed), &consumed, &reduced);
        if (e == NULL) {
            Cudd_IterDerefBdd(manager, t);
            return (NULL);
        }
        cuddRef(e);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
    } else { // first compute else branch
        e = cuddBddAndReducedRecur(manager, fnv, gnv, heu, DD_MIN_NODE_LIMIT(limit), &consumed, &reduced);
        if (e == NULL) { return (NULL); }
        cuddRef(e);
        *nodesConsumed += consumed;
        
        consumed = 0;
        t = cuddBddAndReducedRecur(manager, fv, gv, heu, DD_MIN_NODE_LIMIT(limit - *nodesConsumed), &consumed, &reduced);
        if (t == NULL) {
            Cudd_IterDerefBdd(manager, e);
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
            r = cuddUniqueInter(manager, (int) index, Cudd_Not(t), Cudd_NotCond(e, e != unknown));
            complementRes = 1;
        } else  if (t == unknown && Cudd_IsComplement(e)) { /* Maintain canonical form. */
            r = cuddUniqueInter(manager, (int) index, t, Cudd_Not(e));
            complementRes = 1;
        } else {
            r = cuddUniqueInter(manager, (int) index, t, e);
        }
        
        if (r == NULL) {
          Cudd_IterDerefBdd(manager, t);
          Cudd_IterDerefBdd(manager, e);
          return (NULL);
        }
        
        if (!DD_MAXREF_IS_FLAG_SET(r->ref)) {
          if (limit == 0) {
            cuddDeref(e);
            cuddDeref(t);
            cuddRef(r);
            Cudd_IterDerefBdd(manager, r);
            *resultReduced = 1;
            return(unknown);
          }
          Cudd_Regular(r)->ref = (DD_MAXREF_FLAG_MASK | Cudd_Regular(r)->ref);
          *nodesConsumed += 1;
        }
        
        if (complementRes) {
          r = Cudd_Not(r);
        }
    }
    
    cuddDeref(e);
    cuddDeref(t);
      
    if (!*resultReduced && (F->ref != 1 || G->ref != 1)) {
        cuddCacheInsert2(manager, Cudd_bddAnd, f, g, r);
    }
    return (r);

} /* end of cuddBddAndRecur */




DdNode *
cuddBddXorReducedRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * g,
  DD_TRAV_HEU heu,
  unsigned int limit,
  unsigned int * nodesConsumed,
  unsigned int * resultReduced) {
    DdNode *F, *fv, *fnv, *G, *gv, *gnv;
    DdNode *one, *zero, *unknown, *r, *t, *e;
    int topf, topg;
    unsigned int index;
    unsigned int consumed, reduced;
    
    statLine(manager);
    one = DD_ONE(manager);
    zero = Cudd_Not(one);
    unknown = DD_UNKNOWN(manager);
    consumed = 0, reduced = 0;

    #ifdef DD_DEBUG
    assert(f != Cudd_Not(unknown));
    assert(g != Cudd_Not(unknown));
    #endif

    /* Terminal cases. */
    F = Cudd_Regular(f);
    G = Cudd_Regular(g);
    if (F == unknown || G == unknown) return (unknown);
    if (f > g) { /* Try to increase cache efficiency and simplify tests. */
        DdNode *tmp = f;
        f = g;
        g = tmp;
        F = Cudd_Regular(f);
        G = Cudd_Regular(g);
    }
    if (g == zero) {
        r = cuddBddReduceByNodeLimitRecur(manager, f, heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return (r);
    }
    if (g == one) {
        r = cuddBddReduceByNodeLimitRecur(manager, Cudd_Not(f), heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return (r);
    }
    if (Cudd_IsComplement(f)) {
        f = Cudd_Not(f);
        g = Cudd_Not(g);
    }
    /* Now the first argument is regular. */
    if (f == one) {
        r = cuddBddReduceByNodeLimitRecur(manager, Cudd_Not(g), heu, limit, &consumed, &reduced);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return (r);
    }

    /* At this point f and g are not constant. */

    /* Check cache. */
    // Suppress cache in reduced algorithms
    r = cuddCacheLookup2(manager, Cudd_bddXor, f, g);
    if (r != NULL) {
        cuddRef(r);
        DdNode *res = cuddBddReduceByNodeLimitRecur(manager, r, heu, limit, &consumed, &reduced);
        cuddRef(res);
        Cudd_IterDerefBdd(manager, r);
        cuddDeref(res);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
        return (res);
    }

    checkWhetherToGiveUp(manager);

    /* Here we can skip the use of cuddI, because the operands are known
    ** to be non-constant.
    */
    topf = manager->perm[f->index];
    topg = manager->perm[G->index];

    /* Compute cofactors. */
    if (topf <= topg) {
        index = f->index;
        fv = cuddT(f);
        fnv = cuddE(f);
    } else {
        index = G->index;
        fv = fnv = f;
    }

    if (topg <= topf) {
        gv = cuddT(G);
        gnv = cuddE(G);
        if (Cudd_IsComplement(g)) {
            gv = Cudd_NotCond(gv, gv != unknown);
            gnv = Cudd_NotCond(gnv, gnv != unknown);
        }
    } else {
        gv = gnv = g;
    }

    int decision = heu(manager, f, g, NULL);
    
    if (decision < 0) { // then branch first
        t = cuddBddXorReducedRecur(manager, fv, gv, heu, DD_MIN_NODE_LIMIT(limit), &consumed, &reduced);
        if (t == NULL) { return (NULL); }
        cuddRef(t);
        *nodesConsumed += consumed;

        consumed = 0;
        e = cuddBddXorReducedRecur(manager, fnv, gnv, heu, DD_MIN_NODE_LIMIT(limit - *nodesConsumed), &consumed, &reduced);
        if (e == NULL) {
            Cudd_IterDerefBdd(manager, t);
            return (NULL);
        }
        cuddRef(e);
        *nodesConsumed += consumed;
        *resultReduced |= reduced;
    } else {
        e = cuddBddXorReducedRecur(manager, fnv, gnv, heu, DD_MIN_NODE_LIMIT(limit), &consumed, &reduced);
        if (e == NULL) { return (NULL); }
        cuddRef(e);
        *nodesConsumed += consumed;

        consumed = 0;
        t = cuddBddXorReducedRecur(manager, fv, gv, heu, DD_MIN_NODE_LIMIT(limit - *nodesConsumed), &consumed, &reduced);
        if (t == NULL) {
            Cudd_IterDerefBdd(manager, e);
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
            r = cuddUniqueInter(manager, (int) index, Cudd_Not(t), Cudd_NotCond(e, e != unknown));
            complementRes = 1;
        } else  if (t == unknown && Cudd_IsComplement(e)) { /* Maintain canonical form. */
            r = cuddUniqueInter(manager, (int) index, t, Cudd_Not(e));
            complementRes = 1;
        } else {
            r = cuddUniqueInter(manager, (int) index, t, e);
        }
        
        if (r == NULL) {
            Cudd_IterDerefBdd(manager, t);
            Cudd_IterDerefBdd(manager, e);
            return (NULL);
        }
        
        if (!DD_MAXREF_IS_FLAG_SET(r->ref)) {
          if (limit == 0) {
            cuddDeref(e);
            cuddDeref(t);
            cuddRef(r);
            Cudd_IterDerefBdd(manager, r);
            *resultReduced = 1;
            return(unknown);
          }
          DD_MAXREF_SET_FLAG(r->ref);
          *nodesConsumed += 1;
        }
        
        if (complementRes) {
          r = Cudd_Not(r);
        }
    }
    #ifdef DD_DEBUG
    assert(e != Cudd_Not(unknown));
    assert(t != Cudd_Not(unknown));
    assert(r != Cudd_Not(unknown));
    #endif
    cuddDeref(e);
    cuddDeref(t);
    if (!*resultReduced) {
        cuddCacheInsert2(manager, Cudd_bddXor, f, g, r);
    }
    return (r);

}  /* end of cuddBddXorReducedRecur */

