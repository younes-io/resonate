module ResonateCollections {
  lemma SingletonRemovedNotPresent(ids: set<nat>, id: nat)
    ensures id !in ids - {id}
  {
    assert !(id in ids - {id});
  }

  lemma SingletonAddedPresent(ids: set<nat>, id: nat)
    ensures id in ids + {id}
  {
    assert id in {id};
  }
}
