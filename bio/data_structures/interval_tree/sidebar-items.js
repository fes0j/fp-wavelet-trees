initSidebarItems({"struct":[["Entry","A `find` query on the interval tree does not directly return references to the nodes in the tree, but wraps the fields `interval` and `data` in an `Entry`."],["EntryMut","A `find_mut` query on the interval tree does not directly return references to the nodes in the tree, but wraps the fields `interval` and `data` in an `EntryMut`. Only the data part can be mutably accessed using the `data` method"],["IntervalTree","An interval tree for storing intervals with data"],["IntervalTreeIterator","An `IntervalTreeIterator` is returned by `Intervaltree::find` and iterates over the entries overlapping the query"],["IntervalTreeIteratorMut","An `IntervalTreeIteratorMut` is returned by `Intervaltree::find_mut` and iterates over the entries overlapping the query allowing mutable access to the data `D`, not the `Interval`."]]});