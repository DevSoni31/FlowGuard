"""
Medical data pipeline — three agents demonstrating IFC violation.
Each hop is locally approved. The transitive High → Low flow is UNSAFE.
Mirrors medicalPipeline in InfoFlow.lean.
"""
import json

PIPELINE_CHANNELS = [
    {"name": "diagnostic→summary", "src": "high",   "dst": "medium"},
    {"name": "summary→report",     "src": "medium",  "dst": "low"},
]

class DiagnosticAgent:
    """Reads patient records (High). Summarises for the next agent."""
    def run(self, patient_id: str) -> dict:
        # Reads from PHI database — high confidentiality
        record = {"patient_id": patient_id, "diagnosis": "Type 2 Diabetes", "notes": "..."}
        return {"summary": record, "label": "high"}

class SummaryAgent:
    """Receives High data, produces Medium summary. Locally approved."""
    def run(self, diagnostic_output: dict) -> dict:
        summary = {"condition": diagnostic_output["summary"].get("diagnosis"), "severity": "moderate"}
        return {"summary": summary, "label": "medium"}

class ReportAgent:
    """Receives Medium data, publishes Low report. Locally approved.
    But: the transitive chain High → Low violates noninterference."""
    def run(self, summary_output: dict) -> dict:
        report = {"public_summary": summary_output["summary"].get("condition")}
        return {"report": report, "label": "low"}

if __name__ == "__main__":
    d = DiagnosticAgent().run("P001")
    s = SummaryAgent().run(d)
    r = ReportAgent().run(s)
    print(json.dumps(r, indent=2))