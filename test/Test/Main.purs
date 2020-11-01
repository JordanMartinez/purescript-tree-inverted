module Test.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Partial.Unsafe (unsafePartial)
import Test.Spec (describe, it, pending)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)
import Tree.InvertedTable.Internal (buildTree, pushChild, rootIndex, siblingIndices, singleton)

nilInt :: Array Int
nilInt = []

nilString :: Array String
nilString = []

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter ] do
  describe "Construction" do
    describe "Root only tree via" do
      describe "singleton" do
        it "creates correctly" do
          let rootOnlyTree = singleton "a"
          pure unit
        describe "indices are correct" do
          let rootOnlyTree = singleton "a"
          it "root index refers to itself" do
            rootIndex rootOnlyTree `shouldEqual` 0
          it "should have 0 siblings" do
            (unsafePartial $ siblingIndices 0 rootOnlyTree) `shouldEqual` nilInt
    describe "buildTree" do
      it "creates correctly" do
        let abTree = buildTree "a" (pushChild "b" *> pushChild "c")
        pure unit
      let abTree = buildTree "a" (pushChild "b" *> pushChild "c")
      describe "root indices are correct" do
        it "root index refers to itself" do
          rootIndex abTree `shouldEqual` 0
        it "root should have 0 siblings" do
          (unsafePartial $ siblingIndices 0 abTree) `shouldEqual` nilInt
      describe "first child indices are correct" do
        it "first child should have 1 sibling" do
          (unsafePartial $ siblingIndices 1 abTree) `shouldEqual` [2]
