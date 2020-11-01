module Tree.InvertedTable.Internal
  ( Tree -- constructor intentionally not exported
  , ArrayIndex
  , FromIndex
  , ToIndex
  , ChildIndex
  , ParentIndex
  , RootIndex
  , rootIndex
  , leafIndices
  , deepCopy
  , TreeBuilder -- constructor intentionally not exported
  , singleton
  , buildTree
  , pushBranch
  , pushChild
  -- pushNode intentionally not exported
  , nodeAt
  , parentIndex
  , immediateChildrenIndices
  , recursiveChildrenIndices
  , siblingIndices
  , parentToChildIndexPath
  , rootToChildIndexPath
  , parentToChildDepth
  , isParentOf
  , rootToChildDepth
  , commonParentIndex
  , depth
  , updateNode
  , modifyNode
  , setParentIndex
  , deleteChild
  , deleteBranch
  , findIndices
  -- buildInvertedTable intentionally not exported
  ) where

import Prelude

import Control.Monad.ST (for)
import Control.Monad.ST as ST
import Data.Array (foldl, foldr, length, modifyAt, snoc, unsafeIndex, updateAt, (..))
import Data.Array.NonEmpty (NonEmptyArray, zip)
import Data.Array.NonEmpty as NEA
import Data.Array.ST as STA
import Data.Foldable (for_)
import Data.FoldableWithIndex (foldlWithIndex, forWithIndex_)
import Data.HashSet as HashSet
import Data.Maybe (Maybe(..), fromJust, isJust)
import Data.NonEmpty (foldl1)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)

-- | Models a Tree structure using an inverted table (i.e. rows become
-- | columns and columns become rows). Think of this as a `Map Int a`.
-- | However, the key in the map is the index of the `a` in an array.
-- |
-- | There are two arrays: the `nodes` array that stores the elements
-- | and the `parents` array that stores the corresponding node's parent
-- | index. To get a node's parent node, find that node's index in the
-- | `nodes` array, look up the corresponding element in the `parents`
-- | array, and use the resulting index to get the element in the `nodes`
-- | array.
-- | The root of the tree refers to itself as its parent.
-- |
-- | ```
-- |
-- | --        0  1  2 -- index of element in array
-- |
-- | nodes:   [1, 2, 3]
-- | parents: [0, 0, 0]
-- | ```
-- | ...corresponds to...
-- | ```
-- |     1
-- |    / \
-- |   /   \
-- | 2      3
-- | ```
-- |
-- Change to Tree = Array (Tuple ParentIndex a) ?
newtype Tree a = Tree
  { nodes :: Array a
  , parents :: Array ParentIndex
  }

type ArrayIndex = Int
type FromIndex = Int
type ToIndex = Int
type ChildIndex = Int
type ParentIndex = Int
type RootIndex = Int

rootIndex :: forall a. Tree a -> RootIndex
rootIndex (Tree tree) = foldlWithIndex doFold (-1) tree.parents
  where
    doFold idx acc nextIdx = if idx == nextIdx then idx else acc

leafIndices :: forall a. Tree a -> Array ChildIndex
leafIndices (Tree tree) = do
  let
    lastIdx = (length tree.parents) - 1
    allPossibleIndices = HashSet.fromArray $ 0 .. lastIdx
    indicesWithoutChildren = foldr HashSet.delete allPossibleIndices tree.parents
  HashSet.toArray indicesWithoutChildren

deepCopy :: forall a. Tree a -> Tree a
deepCopy (Tree {nodes, parents}) = Tree $ ST.run do
  let lastIndex = (length nodes) - 1
  out1 <- STA.empty
  out2 <- STA.empty
  for 0 lastIndex \currentIndex -> do
    let el1 = unsafePartial $ unsafeIndex nodes currentIndex
    _ <- STA.push el1 out1

    let el2 = unsafePartial $ unsafeIndex parents currentIndex
    STA.push el2 out2

  finished1 <- STA.unsafeFreeze out1
  finished2 <- STA.unsafeFreeze out2
  pure { nodes: finished1, parents: finished2 }

-- Construction

newtype TreeBuilder h a = TreeBuilder
  ( { nodeArray :: STA.STArray h a
    , parentArray :: STA.STArray h Int
    }
  -> ParentIndex
  -> ST.ST h ArrayIndex
  )

singleton :: forall a. a -> Tree a
singleton a = Tree { nodes: [a], parents: [0] }

buildTree :: forall a. a -> Maybe (forall h. TreeBuilder h a) -> Tree a
buildTree root maybeBuilder = Tree $ ST.run do
  nodeArray <- STA.empty
  parentArray <- STA.empty

  _ <- STA.push root nodeArray
  _ <- STA.push 0 parentArray
  for_ maybeBuilder \(TreeBuilder builder) -> do
    let rec = { nodeArray, parentArray }
    void $ builder rec 0

  nodes <- STA.unsafeFreeze nodeArray
  parents <- STA.unsafeFreeze parentArray

  pure { nodes: [], parents: [] }

pushBranch :: forall h a
   . a -> TreeBuilder h a -> TreeBuilder h a
pushBranch branch (TreeBuilder addChildren) = TreeBuilder \rec parentIdx -> do
  branchIndex <- unsafePartial $ pushNode rec parentIdx branch
  _ <- addChildren rec branchIndex
  pure branchIndex

pushChild :: forall h a
   . a -> TreeBuilder h a
pushChild child = TreeBuilder \rec parentIdx -> do
  unsafePartial $ pushNode rec parentIdx child

pushNode :: forall h a
   . Partial
  => { nodeArray :: STA.STArray h a
     , parentArray :: STA.STArray h Int
     }
  -> ParentIndex
  -> a
  -> ST.ST h ArrayIndex
pushNode rec parentIdx a = do
  len <- STA.push a rec.nodeArray
  _ <- STA.push parentIdx rec.parentArray
  pure (len - 1)

-- Internal

---- Query information

nodeAt :: forall a. Partial => ArrayIndex -> Tree a -> a
nodeAt idx (Tree tree) = unsafeIndex tree.nodes idx

parentIndex :: forall a. Partial => ArrayIndex -> Tree a -> ArrayIndex
parentIndex idx (Tree tree) = unsafeIndex tree.parents idx

immediateChildrenIndices :: forall a. Partial => ArrayIndex -> Tree a -> Array ArrayIndex
immediateChildrenIndices idx (Tree tree) = STA.run do
  arr <- STA.empty
  forWithIndex_ tree.parents \nodeIndex parentIdx -> do
    when (parentIdx == idx) do
      void $ STA.push nodeIndex arr
  pure arr

recursiveChildrenIndices :: forall a. Partial => ParentIndex -> Tree a -> Array ChildIndex
recursiveChildrenIndices parentIdx t@(Tree tree) =
  HashSet.toArray $ foldl doFold HashSet.empty tree.parents
  where
    doFold :: _ -> Int -> _
    doFold set childIdx = do
      case parentToChildIndexPath parentIdx childIdx t of
        Nothing -> set
        Just ar -> foldr HashSet.insert set ar

siblingIndices :: forall a. Partial => ArrayIndex -> Tree a -> Array ArrayIndex
siblingIndices childIdx t@(Tree tree) = foldlWithIndex f [] tree.parents
  where
    parent = parentIndex childIdx t
    f index acc parentIdx =
      if parentIdx == parent && index /= childIdx then acc `snoc` index else acc

parentToChildIndexPath :: forall a. Partial => ParentIndex -> ChildIndex -> Tree a -> Maybe (NonEmptyArray ArrayIndex)
parentToChildIndexPath targetParent originalChild tree = do
  buildIndexPath originalChild (NEA.singleton originalChild)
  where
    buildIndexPath :: ArrayIndex -> NonEmptyArray ArrayIndex -> Maybe (NonEmptyArray ArrayIndex)
    buildIndexPath currentIndex pathSoFar = do
      let
        parent = parentIndex currentIndex tree
        currentPath = NEA.cons parent pathSoFar
        childIsRootIndex = parent == currentIndex
        childParentIsTargetParent = parent == targetParent
      if childIsRootIndex then Nothing
      else if childParentIsTargetParent then Just currentPath
      else buildIndexPath parent currentPath

rootToChildIndexPath :: forall a. Partial => ArrayIndex -> Tree a -> NonEmptyArray ArrayIndex
rootToChildIndexPath idx tree = do
  buildIndexPath idx (NEA.singleton idx)
  where
    buildIndexPath :: ArrayIndex -> NonEmptyArray ArrayIndex -> NonEmptyArray ArrayIndex
    buildIndexPath currentIndex pathSoFar = do
      let
        parent = parentIndex currentIndex tree
        currentPath = NEA.cons parent pathSoFar
      if parent == currentIndex then currentPath
      else
        buildIndexPath parent currentPath

parentToChildDepth :: forall a. Partial => ParentIndex -> ChildIndex -> Tree a -> Maybe Int
parentToChildDepth targetParent originalChild tree = do
  calculateDepth originalChild 0
  where
    calculateDepth :: ArrayIndex -> Int -> Maybe Int
    calculateDepth currentIndex depthSoFar = do
      let
        parent = parentIndex currentIndex tree
        childIsRootIndex = parent == currentIndex
        childParentIsTargetParent = parent == targetParent
      if childIsRootIndex then Nothing
      else if childParentIsTargetParent then Just depthSoFar
      else calculateDepth parent (depthSoFar + 1)

isParentOf :: forall a. Partial => ParentIndex -> ChildIndex -> Tree a -> Boolean
isParentOf targetParent originalChild tree =
  isJust $ parentToChildDepth targetParent originalChild tree

rootToChildDepth :: forall a. Partial => ArrayIndex -> Tree a -> Int
rootToChildDepth idx tree = calculateDepth idx 0
  where
    calculateDepth :: ArrayIndex -> Int -> Int
    calculateDepth currentIndex depthSoFar = do
      let parent = parentIndex currentIndex tree
      if parent == currentIndex then depthSoFar
      else
        calculateDepth parent (depthSoFar + 1)

commonParentIndex :: forall a. Partial => ArrayIndex -> ArrayIndex -> Tree a -> ArrayIndex
commonParentIndex l r tree = do
  let
    lpath = rootToChildIndexPath l tree
    rpath = rootToChildIndexPath r tree
    combo = zip lpath rpath
    lastSharedPath acc next@(Tuple a b) = if a == b then next else acc
    Tuple sharedIdx _ = foldl1 lastSharedPath (NEA.toNonEmpty combo)
  sharedIdx

depth :: forall a. Partial => ArrayIndex -> Tree a -> Int
depth idx tree = NEA.length $ rootToChildIndexPath idx tree

---- Modifications

updateNode :: forall a. Partial => ChildIndex -> a -> Tree a -> Tree a
updateNode idx newValue (Tree tree) =
  Tree tree { nodes = fromJust $ updateAt idx newValue tree.nodes }

modifyNode :: forall a. Partial => ChildIndex -> (a -> a) -> Tree a -> Tree a
modifyNode idx modify (Tree tree) =
  Tree tree { nodes = fromJust $ modifyAt idx modify tree.nodes }

-- Note: when the parent index is a valid index into the array, this is safe
-- to do except in the following cases:
-- 1. the child in question is the root and you set it to something other than
--     itself (i.e. making the tree `root`less, producing an infinite loop).
-- 2. you set the child in question to its own index, thereby making a tree
--     that has two roots.
setParentIndex :: forall a. Partial => ChildIndex -> ParentIndex -> Tree a -> Tree a
setParentIndex childIdx parentIdx (Tree tree) =
  Tree tree { parents = newparents }
  where
    newparents = STA.run do
      stArray <- STA.thaw tree.parents
      _ <- STA.poke childIdx parentIdx stArray
      pure stArray

{-
Three things can happen when deleting a node:
- deleting a leaf: just delete leaf and leave it (no pun intended) as that
- deleting a branch: delete the branch and its children recursively
- deleting the root: can either do nothing or wrap return in Maybe

How deletions could be done:
1 replace element in deleted node's index in `nodes` and `parents` with
  some value that indicates "this no longer exists". While this could work
  the only value we could put into array is either null or Nothing, which
  affects performance due to wrapping
2 delete elements in arrays and update indices, so that indices in `parents`
  still correspond to their nodes in `nodes` and update the parent index in
  `parents` to refer to the updated indices in `nodes`. This is the best
  solution but is difficult to implement correctly

We choose option 2.

When we delete an element in the array, all elements to the right of
  deletion point will reduce their index by 1
    Start:      [0      , 1      , 2         , x      , 4       , 5]
    Deletion:   [0      , 1      , 2         ,        , 4       , 5]
    Shifting:   [0      , 1      , 2         , 4      , 5       ]
    Adjustment: [0      , 1      , 2         , (4 - 1), (5 - 1) ]
    Final:      [0      , 1      , 2         , 3      , 4       ]

This same adjustment will need to be done in the `parents` side.

However, the `parents` side may have refer to indices before and after the
  index of deletion. In such a situation, we need to update those indices
  by reducing them by 1 only if their value is greater than the deleted index.
    Start:      [5      , 4      , 2         , x      , 1       , 5]
    Deletion:   [5      , 4      , 2         ,        , 1       , 5]
    Shifting:   [5      , 4      , 2         , 1      , 5       ]
    Adjustment: [(5 - 1), (4 - 1), 2         , 1      , (5 - 1) ]
    Final:      [4      , 3      , 2         , 1      , 4       ]

When we delete nodes or leaves, we should delete them from the `nodes`
  array and then from the `parents` array bottom-up. We should not batch
  deletions (e.g. all deletions to `nodes` in one go) unless we can prove
  that this is safe to do.

-}
-- runtime error can happen at time X if
-- - we delete all node in the tree (where X is when this function is called)
-- - we delete the root node (where X occurs in later function once this one finishes)
deleteChild :: forall a. Partial => ChildIndex -> Tree a -> Tree a
deleteChild indexToRemove (Tree tree) = Tree { nodes, parents }
  where
    includeIndex idx = idx /= indexToRemove

    shiftIndexLeftIfAfterDeletedNode i =
      if indexToRemove < i then (i - 1) else i

    nodeRec = { array: tree.nodes
              , modify: identity
              }
    parentRec = { array: tree.parents
                , modify: shiftIndexLeftIfAfterDeletedNode
                }
    Tuple nodes parents =
      buildInvertedTable includeIndex (Tuple nodeRec parentRec)

-- Makes a branch's children to be the branch's parent's children and
-- then deletes the branch.
deleteBranch :: forall a. Partial => ChildIndex -> Tree a -> Tree a
deleteBranch indexToRemove t@(Tree tree) = Tree { nodes, parents }
  where
    branchParentIndex = parentIndex indexToRemove t

    includeIndex idx = idx /= indexToRemove
    changeParentToParentsParent i =
      if i == indexToRemove then branchParentIndex else i
    shiftIndexLeftIfAfterDeletedNode i =
      if indexToRemove < i then (i - 1) else i
    adjustRelationIndices =
      changeParentToParentsParent
        >>> shiftIndexLeftIfAfterDeletedNode

    nodeRec = { array: tree.nodes
              , modify: identity
              }
    parentRec = { array: tree.parents
                , modify: adjustRelationIndices
                }
    Tuple nodes parents =
      buildInvertedTable includeIndex (Tuple nodeRec parentRec)


-- Utility functions not found in `purescript-arrays`.

findIndices :: forall a. (a -> Boolean) -> Array a -> Array ArrayIndex
findIndices found arr = STA.run do
    output <- STA.empty
    let lastIdx = (length arr) - 1
    for 0 lastIdx \idx -> do
      let next = unsafePartial $ unsafeIndex arr idx
      when (found next) do
        void $ STA.push idx output
    pure output

{-
What led me here.

Performance-wise, we're iterating over 2 arrays that are of the same size
to do an update to a data strcuture (i.e. `O(2n)`).
Since these will always be the same size, why can't we do this in `O(n)` time
by iterating through each array once in the same iteration.
-}

type IVTArrayRecord a =
  { array :: Array a
  , modify :: a -> a
  }

-- Ideally, the input and output `Tuple` would be `HList`.
buildInvertedTable
  :: forall a b
   . (ChildIndex -> Boolean)
  -> Tuple (IVTArrayRecord a) (IVTArrayRecord b)
  -> (Tuple (Array a) (Array b))
buildInvertedTable include (Tuple first second) = ST.run do
  let lastIndex = (length first.array) - 1
  out1 <- STA.empty
  out2 <- STA.empty
  for 0 lastIndex \currentIndex -> do
    when (include currentIndex) do
      let el1 = unsafePartial $ unsafeIndex first.array currentIndex
      _ <- STA.push (first.modify el1) out1

      let el2 = unsafePartial $ unsafeIndex second.array currentIndex
      void $ STA.push (second.modify el2) out2

  finished1 <- STA.unsafeFreeze out1
  finished2 <- STA.unsafeFreeze out2
  pure (Tuple finished1 finished2)
