// Go implementation of SeedSource.GetSeed (bv64 -> uint64).
// Build/run:  dafny run --target:go SeedSourceDemo.dfy --input SeedSource.go
// (Requires `goimports` on PATH — `go install golang.org/x/tools/cmd/goimports@latest`.)
package SeedSource

import (
	"crypto/rand"
	"encoding/binary"
	"time"
)

func GetSeed() uint64 {
	var b [8]byte
	_, _ = rand.Read(b[:])
	return binary.LittleEndian.Uint64(b[:])
}

// NowNanos returns a nanosecond timestamp; only differences are consumed, so
// the origin (Unix epoch here) is unspecified as far as callers are concerned.
func NowNanos() uint64 {
	return uint64(time.Now().UnixNano())
}
