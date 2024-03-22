package tree_sitter_tlaplus_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-tlaplus"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_tlaplus.Language())
	if language == nil {
		t.Errorf("Error loading Tlaplus grammar")
	}
}
