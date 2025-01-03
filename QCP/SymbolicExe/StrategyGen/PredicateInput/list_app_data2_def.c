/*@ Let(struct list) listrep(l) = l == 0 && emp ||
      exists v u t, data_at(field_addr(l, head), v) * data_at(field_addr(l, data), u) * data_at(field_addr(l, tail), t) * listrep(t)
 */
 
/*@ Let(struct list) lseg(x, y) = x == y && emp ||
      exists v u z, data_at(field_addr(x, head), v) * data_at(field_addr(x, data), u) * data_at(field_addr(x, tail), z) * lseg(z, y)
 */