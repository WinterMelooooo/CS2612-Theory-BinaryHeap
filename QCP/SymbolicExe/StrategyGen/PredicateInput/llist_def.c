/*@ Let(struct llist_node) llistrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * llistrep(t)
 */
 
/*@ Let(struct llist_node) llistseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, next), z) * llistseg(z, y)
 */