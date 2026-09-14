private inductive Html where
  | elem (tag : String) (children : Array Html)
  | text (content : String)
deriving Repr

-- 1. A builder monad that accumulates child nodes into an array
abbrev HtmlM := StateM (Array Html) Unit

-- 2. Automatically lift any `Html` node into the builder monad
private instance : Coe Html HtmlM where
  coe h := modify (·.push h)

-- 3. Base constructors
private def text (content : String) : Html :=
  Html.text content

private def mkElem (tag : String) (children : HtmlM) : Html :=
  let (_, nodes) := children.run #[]
  Html.elem tag nodes

-- 4. HTML tag functions (take a `do` block, return `Html`)
private def section_ (c : HtmlM) : Html := mkElem "section" c
private def article (c : HtmlM) : Html := mkElem "article" c
private def h1 (c : HtmlM)      : Html := mkElem "h1" c
private def h2 (c : HtmlM)      : Html := mkElem "h2" c
private def p (c : HtmlM)       : Html := mkElem "p" c

-- 5. The test function using pure `do` blocks
def test (user : String) : Html := section_ do
  h1 do
    text s!"Posts for {user}"
  article do
    h2 do
      text "The first post"
    p do
      text "This is the first post."
      text "Not much else to say."
