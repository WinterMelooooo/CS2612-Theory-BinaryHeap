struct tree {
    int data;
    struct tree * left;
    struct tree * right;
    struct tree * parent;
};

/*@
  Let tree_rep(p, p_par) = p == 0 && emp ||
  	exists p_lch, 
        exists p_rch, (p -> {tree.left} == p_lch) && (p -> {tree.right} == p_rch) &&
        (p -> {tree.parent} == p_par) && tree_rep(p_lch, p) && tree_rep(p_rch, p)
 */

void malloc_tree (void *p)
/*@ 
    Require emp
    Ensure  (p -> {tree.left} == 0) && (p -> {tree.right} == 0) &&
            (p -> {tree.parent} == 0) && (p -> {tree.data} == 0)
 */;

struct tree * insert(struct tree* x, int v)
/*@ With x_par
    Require tree_rep(x, x_par)
    Ensure tree_rep(__return, x_par)
 */
{
    struct tree * y;
    struct tree * t;
    if (x == (struct tree *)0) {
        x->data = v;
        return x;
    }
    else {
        y = x;
        t = y->parent;
        //@ Inv tree_rep(y, t)
        while (y) {
            t = y;
            if (y->data < v)
                y = y->right;
            else if (y->data > v)
                y = y->left;
            else
                return x;
        }
        malloc_tree(y);
        y->data = v;
        y->parent = t;
        if (t->data < v)
            t->right = y;
        else
            t->left = y;
        return x;
    }
}
