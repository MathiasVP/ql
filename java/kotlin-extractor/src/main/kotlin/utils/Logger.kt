package com.github.codeql

import java.io.File
import java.io.FileWriter
import java.io.OutputStreamWriter
import java.io.Writer
import java.text.SimpleDateFormat
import java.util.Date
import org.jetbrains.kotlin.ir.IrElement

class LogCounter() {
    public val diagnosticCounts = mutableMapOf<String, Int>()
    public val diagnosticLimit: Int
    init {
        diagnosticLimit = System.getenv("CODEQL_EXTRACTOR_KOTLIN_DIAGNOSTIC_LIMIT")?.toIntOrNull() ?: 100
    }
}

enum class Severity(val sev: Int) {
    WarnLow(1),
    Warn(2),
    WarnHigh(3),
    /** Minor extractor errors, with minimal impact on analysis. */
    ErrorLow(4),
    /** Most extractor errors, with local impact on analysis. */
    Error(5),
    /** Javac errors. */
    ErrorHigh(6),
    /** Severe extractor errors affecting a single source file. */
    ErrorSevere(7),
    /** Severe extractor errors likely to affect multiple source files. */
    ErrorGlobal(8)
}

open class LoggerBase(val logCounter: LogCounter) {
    private val logStream: Writer
    init {
        val extractorLogDir = System.getenv("CODEQL_EXTRACTOR_JAVA_LOG_DIR")
        if (extractorLogDir == null || extractorLogDir == "") {
            logStream = OutputStreamWriter(System.out)
        } else {
            val logFile = File.createTempFile("kotlin-extractor.", ".log", File(extractorLogDir))
            logStream = FileWriter(logFile)
        }
    }

    private fun timestamp(): String {
        return "[${SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(Date())} K]"
    }

    private fun getDiagnosticLocation(): String? {
        val st = Exception().stackTrace
        for(x in st) {
            when(x.className) {
                "com.github.codeql.Logger",
                "com.github.codeql.FileLogger" -> {}
                else -> {
                    return x.toString()
                }
            }
        }
        return null
    }

    fun diagnostic(tw: TrapWriter, severity: Severity, msg: String, extraInfo: String?, locationString: String? = null, mkLocationId: () -> Label<DbLocation> = { tw.unknownLocation }) {
        val diagnosticLoc = getDiagnosticLocation()
        val diagnosticLocStr = if(diagnosticLoc == null) "<unknown location>" else diagnosticLoc
        val extraInfoStr = if (extraInfo == null) "" else (extraInfo + "\n")
        val suffix =
            if(diagnosticLoc == null) {
                "    Missing caller information.\n"
            } else {
                val count = logCounter.diagnosticCounts.getOrDefault(diagnosticLoc, 0) + 1
                logCounter.diagnosticCounts[diagnosticLoc] = count
                when {
                    logCounter.diagnosticLimit <= 0 -> ""
                    count == logCounter.diagnosticLimit -> "    Limit reached for diagnostics from $diagnosticLoc.\n"
                    count > logCounter.diagnosticLimit -> return
                    else -> ""
                }
            }
        val fullMsg = "$msg\n$extraInfoStr$suffix"
        val ts = timestamp()
        // We don't actually make the location until after the `return` above
        val locationId = mkLocationId()
        tw.writeDiagnostics(StarLabel(), "CodeQL Kotlin extractor", severity.sev, "", msg, "$ts $fullMsg", locationId)
        val locStr = if (locationString == null) "" else "At " + locationString + ": "
        logStream.write("$ts Diagnostic($diagnosticLocStr): $locStr$fullMsg")
    }

    fun info(tw: TrapWriter, msg: String) {
        val fullMsg = "${timestamp()} $msg"
        tw.writeComment(fullMsg)
        logStream.write(fullMsg + "\n")
    }

    fun warn(tw: TrapWriter, msg: String, extraInfo: String?) {
        diagnostic(tw, Severity.Warn, msg, extraInfo)
    }
    fun error(tw: TrapWriter, msg: String, extraInfo: String?) {
        diagnostic(tw, Severity.Error, msg, extraInfo)
    }

    fun printLimitedDiagnosticCounts(tw: TrapWriter) {
        for((caller, count) in logCounter.diagnosticCounts) {
            if(count >= logCounter.diagnosticLimit) {
                val msg = "Total of $count diagnostics from $caller.\n"
                tw.writeComment(msg)
                logStream.write(msg)
            }
        }
    }

    fun flush() {
        logStream.flush()
    }

    fun close() {
        logStream.close()
    }
}

open class Logger(val loggerBase: LoggerBase, open val tw: TrapWriter) {
    private fun getDiagnosticLocation(): String? {
        val st = Exception().stackTrace
        for(x in st) {
            when(x.className) {
                "com.github.codeql.Logger",
                "com.github.codeql.FileLogger" -> {}
                else -> {
                    return x.toString()
                }
            }
        }
        return null
    }

    fun flush() {
        tw.flush()
        loggerBase.flush()
    }

    fun info(msg: String) {
        loggerBase.info(tw, msg)
    }
    fun trace(msg: String) {
        if(false) {
            info(msg)
        }
    }
    fun debug(msg: String) {
        info(msg)
    }
    fun trace(msg: String, exn: Exception) {
        trace(msg + "\n" + exn.stackTraceToString())
    }

    fun warn(msg: String, exn: Exception) {
        warn(msg, exn.stackTraceToString())
    }
    fun warn(msg: String, extraInfo: String?) {
        loggerBase.warn(tw, msg, extraInfo)
    }
    fun warn(msg: String) {
        warn(msg, null)
    }

    fun error(msg: String, extraInfo: String?) {
        loggerBase.error(tw, msg, extraInfo)
    }
    fun error(msg: String) {
        error(msg, null)
    }
    fun error(msg: String, exn: Exception) {
        error(msg, exn.stackTraceToString())
    }
}

class FileLogger(loggerBase: LoggerBase, override val tw: FileTrapWriter): Logger(loggerBase, tw) {
    fun warnElement(msg: String, element: IrElement) {
        val locationString = tw.getLocationString(element)
        val mkLocationId = { tw.getLocation(element) }
        loggerBase.diagnostic(tw, Severity.Warn, msg, null, locationString, mkLocationId)
    }

    fun errorElement(msg: String, element: IrElement) {
        val locationString = tw.getLocationString(element)
        val mkLocationId = { tw.getLocation(element) }
        loggerBase.diagnostic(tw, Severity.Error, msg, null, locationString, mkLocationId)
    }
}
