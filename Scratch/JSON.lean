import Mathlib
open Std

inductive JSONItem where
  | JSONObject : HashMap.Raw String JSONItem → JSONItem
  | JSONArray : Array JSONItem → JSONItem
  | JSONString : String → JSONItem
  | JSONNumber : ℝ → JSONItem
  | JSONBoolean : Bool → JSONItem
  | JSONNull : JSONItem

open JSONItem

def j1 : JSONItem := JSONArray #[(JSONString "val")]
