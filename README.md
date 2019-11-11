# formalized DFS Algorithm proof
The formalized DFS (Depth First Search) proof is based on the graph libraries of RamifyCoq.

You can fetch the RamifyCoq files in other's repository on Github.

To proof the DFS algorithm, we firstly define ``state`` as a ``(stack, vis_list)`` pair, both ``stack`` and ``vis_list`` is formalized as ``list Vertex``. We defined ``empty_state`` as ``(nil, nil)`` especially. The ``stack`` is the recursive stack of DFS, and the ``vis_list`` includes the vertex which has been visited.

The ``pg`` in the code means PreGraph, as defined in the graph libraries in RamifyCoq, the ``st`` in the code means the starting vertex.

We define ``DFS_step`` as a relation of step to describe every step of DFS, including forwarding (to a new vertex), backwarding (to a previous vertex, in some conditions), and a special step for the start (from ``empty_state`` to the first state).

After the definition of ``DFS_step``,  we use the ``clos_refl_trans`` to connect steps together and define ``DFS``, so that we can get a full DFS process, from ``empty_state`` to the ``end_state`` (the definition of ``end_state`` will be explained later).

We proof some simple lemma first, such as:

- ``DFS_step`` change the state: ``Lemma step_change``
- ``vis_list`` is not empty: ``Lemma vis_list_not_empty``
- The length of ``vis_list`` is increasing: ``Lemma vis_list_length_incr``
- The ``DFS_step`` and ``DFS`` process only add vertex to the ``vis_list``:``Lemma vis_list_add_step``,``Lemma vis_list_add``
- The starting vertex must be in every state's ``vis_list``: ``Lemma st_in_vis_list``
- The vertex in recursive ``stack`` must be in ``vis_list``: ``Lemma in_stack_in_vis_list``

Then we proof the important theorem: All vertex in ``vis_list`` must be reachable from ``st`` in ``Theorem vis_list_all_reachable``, the simple proof of the theorem use some of the lemmas above.

```Coq
Theorem vis_list_all_reachable: forall s,
  DFS empty_state s ->
    (forall v, In v (snd s) -> reachable pg st v).
```

Then we proof an useless lemma:

- For every vertex, there must be a state where it firstly enters in the ``stack`` and the ``vis_list``: ``Lemma in_vis_list_once_in``

Use the method of the last lemma, we can have the important lemma below:

- For every vertex, there must be a state where it firstly **leaves** the ``stack``:  ``Lemma in_vis_list_once_out``

With the help of the important lemma, we can easily proof the lemmas like:``Lemma reachable_vis_list_strong_edge``, ``Lemma reachable_vis_list_strong``.

Then we define the ``end_state`` as a state that can't go anywhere.

We proof that in the end_state, the ``stack`` is empty: ``Lemma end_state_stack_empty``, and ``vis_list`` is not empty: ``Lemma end_state_vis_list_not_empty``.

Then we can use the above lemmas to complete the proof of DFS by proving the following important theorem: All vertex reachable from starting vertex must be in ``vis_list`` in the end.

```Coq
Theorem reachable_vis_list: forall v s, vvalid pg st -> 
  DFS empty_state s -> 
    end_state s ->
      reachable pg st v -> In v (snd s).
```

Combined the theorems above, we prove that DFS is correct.



