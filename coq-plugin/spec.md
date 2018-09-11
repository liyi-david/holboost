### tasks
#### task

A task is a goal to solve, together with its environment (both local and global) and evar_map.

```
{
    "env": {},
    "sigma": {},
    "goal" : <term as json>
}
```

### terms
#### sort

`Prop`, `Set` and `Type` are called sorts. They are the most primitive types in Coq's type system. In the exported json strings, they are descripted by:

```
{ "type" : "sort", "sort" : "set" }
{ "type" : "sort", "sort" : "prop" }
{ "type" : "sort", "sort" : "type" }
```
