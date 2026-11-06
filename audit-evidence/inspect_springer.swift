// Local-only extraction/rendering. Never add the input, text, or images to Git.
// swift -module-cache-path .local-sources/swift-cache audit-evidence/inspect_springer.swift
import Foundation
import PDFKit
import AppKit

let root = URL(fileURLWithPath: FileManager.default.currentDirectoryPath)
let local = root.appendingPathComponent(".local-sources")
let input = local.appendingPathComponent("additive-number-theory-2010.pdf")
guard let doc = PDFDocument(url: input) else { fatalError("Cannot read local PDF") }
print("PDF pages: \(doc.pageCount)")
var text = ""
for i in 0..<doc.pageCount {
    let pageText = doc.page(at: i)?.string ?? ""
    text += "\n=== PDF PAGE \(i + 1) ===\n\(pageText)\n"
    if pageText.contains("Theorem 1.5") || pageText.contains("Proof of Theorem 1.5") {
        print("Theorem 1.5 text on PDF page \(i + 1)")
    }
}
try text.write(to: local.appendingPathComponent("springer-pdfkit.txt"), atomically: true, encoding: .utf8)
// Pass one-based PDF page numbers after the script to render selected pages.
for arg in CommandLine.arguments.dropFirst() {
    guard let n = Int(arg), let page = doc.page(at: n - 1) else { fatalError("Invalid page") }
    let img = page.thumbnail(of: NSSize(width: 1600, height: 2200), for: .mediaBox)
    guard let tiff = img.tiffRepresentation, let rep = NSBitmapImageRep(data: tiff),
          let png = rep.representation(using: .png, properties: [:]) else { fatalError("Cannot render") }
    let target = local.appendingPathComponent("springer-page-\(n).png")
    try png.write(to: target)
    print("Rendered \(target.lastPathComponent)")
}
