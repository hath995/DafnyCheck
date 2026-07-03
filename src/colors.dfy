

module ConsoleColors {
        //https://www.shellhacks.com/bash-colors/
        const RL_START_IGNORE := 1 as char
        const RL_END_IGNORE := 2 as char
        const escape: char := 27 as char
        
        // Helper function to create an ANSI escape sequence
        function makeColor(code: string): string {
            [escape] + code
        }
        
        // Helper function to combine foreground and background codes
        // bgCode format: "[40m", fgCode format: "[1;31m" or "[31m"
        // Result: "[40;1;31m" or "[40;31m"
        function combineColors(fgCode: string, bgCode: string): string
            requires |bgCode| >= 3 && bgCode[0] == '[' && bgCode[|bgCode|-1] == 'm'
            requires |fgCode| >= 3 && fgCode[0] == '[' && fgCode[|fgCode|-1] == 'm'
        {
            // Extract numeric part from bgCode: "[40m" -> "40"
            var bgNum := bgCode[1..|bgCode|-1];
            // Extract numeric part from fgCode: "[1;31m" -> "1;31" or "[31m" -> "31"
            var fgNum := fgCode[1..|fgCode|-1];
            // Combine: "[40;1;31m"
            var combined := "[" + bgNum + ";" + fgNum + "m";
            makeColor(combined)
        }
        
        // Raw ANSI codes (without escape wrapper) for combining
        const FG_BLACK_CODE := "[1;30m"
        const FG_RED_CODE := "[1;31m"
        const FG_GREEN_CODE := "[1;32m"
        const FG_YELLOW_CODE := "[1;33m"
        const FG_BLUE_CODE := "[1;34m"
        const FG_MAGENTA_CODE := "[1;35m"
        const FG_CYAN_CODE := "[1;36m"
        const FG_WHITE_CODE := "[1;37m"
        
        const FG_BLACK_NORMAL_CODE := "[30m"
        const FG_RED_NORMAL_CODE := "[31m"
        const FG_GREEN_NORMAL_CODE := "[32m"
        const FG_YELLOW_NORMAL_CODE := "[33m"
        const FG_BLUE_NORMAL_CODE := "[34m"
        const FG_MAGENTA_NORMAL_CODE := "[35m"
        const FG_CYAN_NORMAL_CODE := "[36m"
        const FG_WHITE_NORMAL_CODE := "[37m"
        
        const BG_BLACK_CODE := "[40m"
        const BG_RED_CODE := "[41m"
        const BG_GREEN_CODE := "[42m"
        const BG_YELLOW_CODE := "[43m"
        const BG_BLUE_CODE := "[44m"
        const BG_MAGENTA_CODE := "[45m"
        const BG_CYAN_CODE := "[46m"
        const BG_WHITE_CODE := "[47m"
        
        // Foreground colors (bright/bold)
        const BLACK := makeColor(FG_BLACK_CODE)
        const RED := makeColor(FG_RED_CODE)
        const GREEN := makeColor(FG_GREEN_CODE)
        const YELLOW := makeColor(FG_YELLOW_CODE)
        const BLUE := makeColor(FG_BLUE_CODE)
        const MAGENTA := makeColor(FG_MAGENTA_CODE)
        const CYAN := makeColor(FG_CYAN_CODE)
        const WHITE := makeColor(FG_WHITE_CODE)
        
        // Foreground colors (normal)
        const BLACK_NORMAL := makeColor(FG_BLACK_NORMAL_CODE)
        const RED_NORMAL := makeColor(FG_RED_NORMAL_CODE)
        const GREEN_NORMAL := makeColor(FG_GREEN_NORMAL_CODE)
        const YELLOW_NORMAL := makeColor(FG_YELLOW_NORMAL_CODE)
        const BLUE_NORMAL := makeColor(FG_BLUE_NORMAL_CODE)
        const MAGENTA_NORMAL := makeColor(FG_MAGENTA_NORMAL_CODE)
        const CYAN_NORMAL := makeColor(FG_CYAN_NORMAL_CODE)
        const WHITE_NORMAL := makeColor(FG_WHITE_NORMAL_CODE)
        
        // Background colors
        const BG_BLACK := makeColor(BG_BLACK_CODE)
        const BG_RED := makeColor(BG_RED_CODE)
        const BG_GREEN := makeColor(BG_GREEN_CODE)
        const BG_YELLOW := makeColor(BG_YELLOW_CODE)
        const BG_BLUE := makeColor(BG_BLUE_CODE)
        const BG_MAGENTA := makeColor(BG_MAGENTA_CODE)
        const BG_CYAN := makeColor(BG_CYAN_CODE)
        const BG_WHITE := makeColor(BG_WHITE_CODE)
        
        // Reset/No color
        const NOCOLOR := makeColor("[0m")
        
        // Combined color function for common combinations
        function FgOnBg(fgCode: string, bgCode: string): string
            requires |bgCode| >= 3 && bgCode[0] == '[' && bgCode[|bgCode|-1] == 'm'
            requires |fgCode| >= 3 && fgCode[0] == '[' && fgCode[|fgCode|-1] == 'm'
        {
            combineColors(fgCode, bgCode)
        }

}