module Tree.InvertedTable where

import Prelude

import Control.Monad.ST (for)
import Control.Monad.ST as ST
import Data.Array (foldr, length, modifyAt, snoc, unsafeIndex, updateAt, (..))
import Data.Array.NonEmpty (NonEmptyArray, zip)
import Data.Array.NonEmpty as NEA
import Data.Array.ST as STA
import Data.FoldableWithIndex (foldlWithIndex, forWithIndex_)
import Data.HashSet as HashSet
import Data.Maybe (fromJust)
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
-- | parents: [0, 1, 1]
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

rootIndex :: forall a. Tree a -> ArrayIndex
rootIndex (Tree tree) = foldlWithIndex doFold (-1) tree.parents
  where
    doFold idx acc nextIdx = if idx == nextIdx then idx else acc

leafIndices :: forall a. Tree a -> Array ArrayIndex
leafIndices (Tree tree) = do
  let
    lastIdx = (length tree.parents) - 1
    allPossibleIndices = HashSet.fromArray $ 0 .. lastIdx
    indicesWithoutChildren = foldr HashSet.delete allPossibleIndices tree.parents
  HashSet.toArray indicesWithoutChildren

-- Construction

newtype TreeBuilderZipper a = TreeBuilderZipper
  { tree :: Tree a
  , focus :: ParentIndex
  }

newtype TreeBuilder h a =
  TreeBuilder (TreeBuilderZipper a -> TreeBuilderZipper a)

deepCopy :: forall a. Tree a -> Tree a
deepCopy (Tree tree) = Tree
  { nodes: deepCopyArray tree.nodes
  , parents: deepCopyArray tree.parents
  }

buildTree :: forall a. a -> (forall h. TreeBuilder h a) -> Tree a
buildTree root (TreeBuilder builder) = do
  let
    TreeBuilderZipper finished =
      -- This is safe to do because we constructed the arrays here and
      -- will not use them until after we have mutated them.
      unsafePartial (builder zipper)
  finished.tree
  where
    tree = Tree { nodes: [root], parents: [0] } -- array construction
    zipper = TreeBuilderZipper { tree, focus: 0 }

addBranchChild :: forall h a. Partial => a -> TreeBuilder h a -> TreeBuilder h a
addBranchChild parent (TreeBuilder addChildren) = TreeBuilder \(TreeBuilderZipper zipper) -> do
  let
    Tuple parentIndex treeWithParent = pushChild parent zipper.focus zipper.tree
    TreeBuilderZipper allDone = addChildren (TreeBuilderZipper { tree: treeWithParent, focus: parentIndex })
  TreeBuilderZipper allDone { focus = zipper.focus }

addLeafChild :: forall h a. Partial => a -> TreeBuilder h a
addLeafChild a = TreeBuilder \(TreeBuilderZipper zipper) -> do
  let
    Tuple newFocus newTree = pushChild a zipper.focus zipper.tree
  TreeBuilderZipper { tree: newTree, focus: newFocus }

-- This function is partial because it uses `unsafeThaw`. It should only be
-- used on `Tree`s that were constructed correctly within this file
-- or after one has made a `deepCopy` of a `Tree`.
pushChild :: forall a. Partial => a -> ParentIndex -> Tree a -> Tuple ChildIndex (Tree a)
pushChild a parentIdx (Tree tree) = do
  let
    Tuple leafIdx nodes = ST.run do
        arr <- STA.unsafeThaw tree.nodes
        len <- STA.push a arr
        safeArray <- STA.unsafeFreeze arr
        pure (Tuple (len - 1) safeArray)
    newTree = Tree
      { nodes
      , parents: STA.run do
          arr <- STA.unsafeThaw tree.parents
          _ <- STA.push parentIdx arr
          pure arr
      }
  Tuple leafIdx newTree

-- Internal

valueAt :: forall a. Partial => ArrayIndex -> Tree a -> a
valueAt idx (Tree tree) = unsafeIndex tree.nodes idx

parentIndex :: forall a. Partial => ArrayIndex -> Tree a -> ArrayIndex
parentIndex idx (Tree tree) = unsafeIndex tree.parents idx

childrenIndices :: forall a. Partial => ArrayIndex -> Tree a -> Array ArrayIndex
childrenIndices idx (Tree tree) = STA.run do
  arr <- STA.empty
  forWithIndex_ tree.parents \nodeIndex parentIdx -> do
    when (parentIdx == idx) do
      void $ STA.push nodeIndex arr
  pure arr

siblingIndices :: forall a. Partial => ArrayIndex -> Tree a -> Array ArrayIndex
siblingIndices childIdx theTree@(Tree tree) = foldlWithIndex f [] tree.parents
  where
    parent = parentIndex childIdx theTree
    f index acc parentIdx =
      if parentIdx == parent && index /= childIdx then acc `snoc` index else acc

updateNode :: forall a. Partial => ChildIndex -> a -> Tree a -> Tree a
updateNode idx newValue (Tree tree) =
  Tree tree { nodes = fromJust $ updateAt idx newValue tree.nodes }

modifyNode :: forall a. Partial => ChildIndex -> (a -> a) -> Tree a -> Tree a
modifyNode idx modify (Tree tree) =
  Tree tree { nodes = fromJust $ modifyAt idx modify tree.nodes }

setParentIndex :: forall a. Partial => ChildIndex -> ParentIndex -> Tree a -> Tree a
setParentIndex childIdx parentIdx (Tree tree) =
  Tree tree { parents = newparents }
  where
    newparents = STA.run do
      stArray <- STA.thaw tree.parents
      _ <- STA.poke childIdx parentIdx stArray
      pure stArray

rootToChildIndexPath :: forall a. Partial => ArrayIndex -> Tree a -> NonEmptyArray ArrayIndex
rootToChildIndexPath idx tree@(Tree rec) = do
  let
    parent = parentIndex idx tree
    currentPath = NEA.singleton idx
  if parent == idx
    then currentPath
    else buildIndexPath parent currentPath
  where
    buildIndexPath :: ArrayIndex -> NonEmptyArray ArrayIndex -> NonEmptyArray ArrayIndex
    buildIndexPath currentIndex pathSoFar = do
      let
        parent = parentIndex currentIndex tree
        currentPath = NEA.cons parent pathSoFar
      if parent == currentIndex then currentPath
      else
        buildIndexPath parent currentPath

childToRootIndexPath :: forall a. Partial => ArrayIndex -> Tree a -> NonEmptyArray ArrayIndex
childToRootIndexPath idx tree =
  NEA.reverse $ rootToChildIndexPath idx tree

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

-- Utility functions not found in `purescript-arrays`.

findIndices :: forall a. (a -> Boolean) -> Array a -> Array ArrayIndex
findIndices found arr = STA.run do
    ar <- STA.empty
    let lastIdx = (length arr) - 1
    for 0 lastIdx \idx -> do
      let next = unsafePartial $ unsafeIndex arr idx
      when (found next) do
        void $ STA.push idx ar
    pure ar

deepCopyArray :: forall a. Array a -> Array a
deepCopyArray arr = STA.run (STA.thaw arr)
