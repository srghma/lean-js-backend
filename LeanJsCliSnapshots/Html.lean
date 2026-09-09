inductive Html where
  | elem (tag : String) (children : List Html)
  | text (content : String)
deriving Repr

def render : Html → String
  | .text content => s!"Html.text {repr content}"
  | .elem tag children =>
      let childrenStr := String.intercalate ", " (children.map render)
      s!"Html.elem {repr tag} [{childrenStr}]"

def test (user : String) : Html :=
  Html.elem "section"
    [ Html.elem "h1" [Html.text ("Posts for " ++ user)]
    , Html.elem "article"
        [ Html.elem "h2" [Html.text "The first post"]
        , Html.elem "p"
            [ Html.text "This is the first post."
            , Html.text "Not much else to say."
            ]
        ]
    ]
