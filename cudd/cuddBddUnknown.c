/**
  @file 

  @ingroup cudd

  @brief Functions for manipulating 3-valued BDDs.

  @author Matej Pavlik
*/

#include "cuddInt.h"

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
