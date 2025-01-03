/*@ Let(struct list) listrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head_), v) * data_at(field_addr(l, tail_), t) * listrep(t)
 */
 
/*@ Let(struct list) lseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(l, head_), v) * data_at(field_addr(x, tail_), z) * lseg(z, y)
 */

/*@ Let(struct listlist) listlistrep(l) = l == 0 && emp ||
      exists v t, data_at(field_addr(l, head), v) * listrep(v) * data_at(field_addr(l, tail), t) * listlistrep(t)
 */
 
/*@ Let(struct listlist) listlseg(x, y) = x == y && emp ||
      exists v z, data_at(field_addr(x, head), v) * listrep(v) * data_at(field_addr(x, tail), z) * listlseg(z, y)
 */