-- | Grapheme Cluster Break property.
module GraphemeClusterBreak
    ( GraphemeClusterBreak(..)
    ) where


-- | @Grapheme_Cluster_Break@ property values as described in
-- [Table 2 of UAX29: Unicode Text Segmentation](http://unicode.org/reports/tr29/#Grapheme_Cluster_Break_Property_Values).
data GraphemeClusterBreak
    = CR
    | LF
    | Control
    | Extend
    | ZWJ
    | RegionalIndicator
    | Prepend
    | SpacingMark
    | L
    | V
    | T
    | LV
    | LVT
    | EBase
    | EModifier
    | GlueAfterZwj
    | EBaseGAZ
    | None
    deriving (Eq, Ord, Bounded, Enum, Show)