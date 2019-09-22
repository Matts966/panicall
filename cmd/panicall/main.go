package main

import (
	"github.com/Matts966/panicall"
	"golang.org/x/tools/go/analysis/singlechecker"
)

func main() { singlechecker.Main(panicall.Analyzer) }
