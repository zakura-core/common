import Darwin
import Foundation
import XCTest

final class OrchardBenchmarkTests: XCTestCase {
    func testTwoActionProver() throws {
        let hardware = hardwareIdentifier()
        let details = deviceDetails(for: hardware)
        let osVersion = UIDevice.current.systemVersion
        let processors = ProcessInfo.processInfo.activeProcessorCount
        let thermalStart = thermalStateName(ProcessInfo.processInfo.thermalState)

        // Rayon reads this before constructing its global pool. Using every
        // logical CPU matches the production multicore default while recording
        // the exact count. iOS provides no supported core-affinity API.
        setenv("RAYON_NUM_THREADS", String(processors), 1)

        let resultPointer = hardware.withCString { hardwarePointer in
            details.model.withCString { modelPointer in
                details.soc.withCString { socPointer in
                    osVersion.withCString { osPointer in
                        thermalStart.withCString { thermalPointer in
                            orchard_ios_benchmark_run(
                                hardwarePointer,
                                modelPointer,
                                socPointer,
                                osPointer,
                                thermalPointer,
                                processors
                            )
                        }
                    }
                }
            }
        }
        let pointer = try XCTUnwrap(resultPointer)
        defer { orchard_ios_benchmark_string_free(pointer) }

        let rustJSON = String(cString: pointer)
        let rustData = try XCTUnwrap(rustJSON.data(using: .utf8))
        var object = try XCTUnwrap(
            JSONSerialization.jsonObject(with: rustData) as? [String: Any]
        )
        if let error = object["error"] as? String {
            XCTFail("Rust benchmark failed: \(error)")
            return
        }

        var device = try XCTUnwrap(object["device"] as? [String: Any])
        device["thermal_state_end"] = thermalStateName(
            ProcessInfo.processInfo.thermalState
        )
        object["device"] = device

        let output = try JSONSerialization.data(
            withJSONObject: object,
            options: [.sortedKeys]
        )
        let json = try XCTUnwrap(String(data: output, encoding: .utf8))

        let attachment = XCTAttachment(
            data: output,
            uniformTypeIdentifier: "public.json"
        )
        attachment.name = "orchard-benchmark.json"
        attachment.lifetime = .keepAlways
        add(attachment)

        print("ORCHARD_BENCHMARK_JSON_BEGIN")
        print("ORCHARD_BENCHMARK_JSON=\(json)")
        print("ORCHARD_BENCHMARK_JSON_END")
    }

    private func hardwareIdentifier() -> String {
        var systemInfo = utsname()
        uname(&systemInfo)
        return withUnsafePointer(to: &systemInfo.machine) { pointer in
            pointer.withMemoryRebound(to: CChar.self, capacity: 1) {
                String(cString: $0)
            }
        }
    }

    private func deviceDetails(for hardware: String) -> (model: String, soc: String) {
        switch hardware {
        case "iPhone16,1":
            return ("iPhone 15 Pro", "A17 Pro")
        case "iPhone16,2":
            return ("iPhone 15 Pro Max", "A17 Pro")
        case "iPhone17,1":
            return ("iPhone 16 Pro", "A18 Pro")
        case "iPhone17,2":
            return ("iPhone 16 Pro Max", "A18 Pro")
        case "iPhone17,3":
            return ("iPhone 16", "A18")
        case "iPhone17,4":
            return ("iPhone 16 Plus", "A18")
        case "iPhone18,1":
            return ("iPhone 17 Pro", "A19 Pro")
        case "iPhone18,2":
            return ("iPhone 17 Pro Max", "A19 Pro")
        case "iPhone18,3":
            return ("iPhone 17", "A19")
        case "iPhone18,4":
            return ("iPhone Air", "A19 Pro")
        default:
            return (hardware, "unknown")
        }
    }

    private func thermalStateName(_ state: ProcessInfo.ThermalState) -> String {
        switch state {
        case .nominal:
            return "nominal"
        case .fair:
            return "fair"
        case .serious:
            return "serious"
        case .critical:
            return "critical"
        @unknown default:
            return "unknown"
        }
    }
}
