include "../src/colors.dfy"

// Visual smoke test for the ANSI color palette, extracted from src/colors.dfy
// (test methods live under test/, not in the library source). Run with:
//   dafny test ../src/colors.dfy ColorsTest.dfy --standard-libraries --allow-warnings
module ColorsTest {
    import opened ConsoleColors

    // @Test
    method TestColors() {
        print "=== Foreground Colors (Bright/Bold) ===\n";
        print BLACK, "BLACK", NOCOLOR, "  ";
        print RED, "RED", NOCOLOR, "  ";
        print GREEN, "GREEN", NOCOLOR, "  ";
        print YELLOW, "YELLOW", NOCOLOR, "  ";
        print BLUE, "BLUE", NOCOLOR, "  ";
        print MAGENTA, "MAGENTA", NOCOLOR, "  ";
        print CYAN, "CYAN", NOCOLOR, "  ";
        print WHITE, "WHITE", NOCOLOR, "\n";

        print "\n=== Foreground Colors (Normal) ===\n";
        print BLACK_NORMAL, "BLACK_NORMAL", NOCOLOR, "  ";
        print RED_NORMAL, "RED_NORMAL", NOCOLOR, "  ";
        print GREEN_NORMAL, "GREEN_NORMAL", NOCOLOR, "  ";
        print YELLOW_NORMAL, "YELLOW_NORMAL", NOCOLOR, "  ";
        print BLUE_NORMAL, "BLUE_NORMAL", NOCOLOR, "  ";
        print MAGENTA_NORMAL, "MAGENTA_NORMAL", NOCOLOR, "  ";
        print CYAN_NORMAL, "CYAN_NORMAL", NOCOLOR, "  ";
        print WHITE_NORMAL, "WHITE_NORMAL", NOCOLOR, "\n";

        print "\n=== Background Colors ===\n";
        print BG_BLACK, "BG_BLACK", NOCOLOR, "  ";
        print BG_RED, "BG_RED", NOCOLOR, "  ";
        print BG_GREEN, "BG_GREEN", NOCOLOR, "  ";
        print BG_YELLOW, "BG_YELLOW", NOCOLOR, "  ";
        print BG_BLUE, "BG_BLUE", NOCOLOR, "  ";
        print BG_MAGENTA, "BG_MAGENTA", NOCOLOR, "  ";
        print BG_CYAN, "BG_CYAN", NOCOLOR, "  ";
        print BG_WHITE, "BG_WHITE", NOCOLOR, "\n";

        print "\n=== Color Grid (Foreground) ===\n";
        var colors := [BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE];
        var names := ["BLACK", "RED", "GREEN", "YELLOW", "BLUE", "MAGENTA", "CYAN", "WHITE"];
        var i := 0;
        while i < |colors| {
            print colors[i], "ABC", NOCOLOR, " ";
            i := i + 1;
        }
        print "\n";
        i := 0;
        while i < |names| {
            print names[i], "  ";
            i := i + 1;
        }
        print "\n";

        print "\n=== Color Grid (Background) ===\n";
        var bgColors := [BG_BLACK, BG_RED, BG_GREEN, BG_YELLOW, BG_BLUE, BG_MAGENTA, BG_CYAN, BG_WHITE];
        var bgNames := ["BG_BLACK", "BG_RED", "BG_GREEN", "BG_YELLOW", "BG_BLUE", "BG_MAGENTA", "BG_CYAN", "BG_WHITE"];
        i := 0;
        while i < |bgColors| {
            print bgColors[i], "   ", NOCOLOR, " ";
            i := i + 1;
        }
        print "\n";
        i := 0;
        while i < |bgNames| {
            print bgNames[i], "  ";
            i := i + 1;
        }
        print "\n";

        print "\n=== Colored Text on Colored Backgrounds ===\n";
        print "Red text on white background: ";
        print FgOnBg(FG_RED_CODE, BG_WHITE_CODE), "Hello", NOCOLOR, "\n";

        print "Green text on black background: ";
        print FgOnBg(FG_GREEN_CODE, BG_BLACK_CODE), "Hello", NOCOLOR, "\n";

        print "Yellow text on blue background: ";
        print FgOnBg(FG_YELLOW_CODE, BG_BLUE_CODE), "Hello", NOCOLOR, "\n";

        print "Cyan text on red background: ";
        print FgOnBg(FG_CYAN_CODE, BG_RED_CODE), "Hello", NOCOLOR, "\n";

        print "White text on magenta background: ";
        print FgOnBg(FG_WHITE_CODE, BG_MAGENTA_CODE), "Hello", NOCOLOR, "\n";

        print "Blue text on yellow background: ";
        print FgOnBg(FG_BLUE_CODE, BG_YELLOW_CODE), "Hello", NOCOLOR, "\n";

        print "\n=== Color Combinations Grid ===\n";
        var fgCodes := [FG_RED_CODE, FG_GREEN_CODE, FG_YELLOW_CODE, FG_BLUE_CODE, FG_MAGENTA_CODE, FG_CYAN_CODE, FG_WHITE_CODE];
        var fgNames := ["RED", "GREEN", "YELLOW", "BLUE", "MAGENTA", "CYAN", "WHITE"];
        var bgCodes := [BG_BLACK_CODE, BG_RED_CODE, BG_GREEN_CODE, BG_BLUE_CODE, BG_MAGENTA_CODE, BG_CYAN_CODE, BG_WHITE_CODE];
        var bgNames2 := ["BG_BLACK", "BG_RED", "BG_GREEN", "BG_BLUE", "BG_MAGENTA", "BG_CYAN", "BG_WHITE"];

        var fgIdx := 0;
        while fgIdx < |fgCodes| {
            var bgIdx := 0;
            while bgIdx < |bgCodes| {
                print FgOnBg(fgCodes[fgIdx], bgCodes[bgIdx]), "X", NOCOLOR, " ";
                bgIdx := bgIdx + 1;
            }
            print " ", fgNames[fgIdx], "\n";
            fgIdx := fgIdx + 1;
        }
        print " ";
        var bgIdx2 := 0;
        while bgIdx2 < |bgNames2| {
            print bgNames2[bgIdx2], " ";
            bgIdx2 := bgIdx2 + 1;
        }
        print "\n";
        print "\n", RED, "RED", NOCOLOR, "\n";
    }
}
