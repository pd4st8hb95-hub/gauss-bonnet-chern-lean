/- Failing on nightly-2025-12-18
import Batteries.Data.String.AsciiCasing

#guard "ABC".caseFoldAsciiOnly == "abc"
#guard "x".caseFoldAsciiOnly != "y"
#guard "Àà".caseFoldAsciiOnly == "Àà"
#guard "1$#!".caseFoldAsciiOnly == "1$#!"

#guard "abc".beqCaseInsensitiveAsciiOnly "ABC" == true
#guard "cba".beqCaseInsensitiveAsciiOnly "ABC" == false
#guard "a".beqCaseInsensitiveAsciiOnly "a" == true
#guard "$".beqCaseInsensitiveAsciiOnly "$" == true
#guard "a".beqCaseInsensitiveAsciiOnly "b" == false
#guard "γ".beqCaseInsensitiveAsciiOnly "Γ" == false
#guard "ä".beqCaseInsensitiveAsciiOnly "Ä" == false

#guard  "abc".cmpCaseInsensitiveAsciiOnly "ABC" == .eq
#guard  "abc".cmpCaseInsensitiveAsciiOnly "xyz" == .lt
#guard  "a".cmpCaseInsensitiveAsciiOnly "a" == .eq
#guard  "$".cmpCaseInsensitiveAsciiOnly "$" == .eq
#guard  "a__".cmpCaseInsensitiveAsciiOnly "b__" == .lt
#guard  "γ".cmpCaseInsensitiveAsciiOnly "Γ" == .gt
#guard  "ä".cmpCaseInsensitiveAsciiOnly "Ä" == .gt

#guard [
  ("", ""),
  ("  ", "  "),
  ("a", "A"),
  ("abc", "ABC"),
  ("aBc", "AbC"),
  ("123", "123"),
  ("国际化与本地化", "国际化与本地化"),
  ("ABC😂🔰🍑xyz", "abc😂🔰🍑XYZ")
].all (fun (a, b) => a.beqCaseInsensitiveAsciiOnly b && a.cmpCaseInsensitiveAsciiOnly b = .eq)

#guard [
  ("国际化", "国际化与本地化"),
  ("", " "),
  ("a", "b"),
  ("ab", "ba"),
  ("123", "124"),
  ("😂", "🍑"),
  ("🔰🍑", "😂🔰🍑aaa")
] |>.all fun (a, b) =>
  a ≠ b && !(a.beqCaseInsensitiveAsciiOnly b) && a.cmpCaseInsensitiveAsciiOnly b != .eq
-/
