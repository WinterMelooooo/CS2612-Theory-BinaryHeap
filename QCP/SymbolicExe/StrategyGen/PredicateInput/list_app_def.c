/*@ Let(struct list) listrep(l) = l == 0 && emp ||
      exists t, data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let(struct list) lseg(x, y) = x == y && emp ||
      exists z, data_at(field_addr(x, tail), z) * lseg(z, y)
 */