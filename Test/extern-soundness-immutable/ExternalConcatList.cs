namespace Collections {

  class ConcatList: DafnyCollections.List {
    readonly DafnyCollections.List left;
    readonly DafnyCollections.List right;

    public ConcatList(DafnyCollections.List left, DafnyCollections.List right) {
      this.left = left;
      this.right = right;
    }

    public ulong Length() {
      return left.Length() + right.Length();
    }
    
    public byte Get(ulong i) {
      if (i < left.Length()) {
        return left.Get(i);
      } else {
        return right.Get(i - left.Length());
      }
    }
  }
}