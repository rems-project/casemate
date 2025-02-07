import pathlib
import base64
import subprocess

HERE = pathlib.Path(__file__).parent
DOC_ROOT = HERE.parent

DOCINFO_TEMPLATE = HERE / "docinfo.template"
LOGO = DOC_ROOT / "logo" / "casemate_logo.png"

b64_logo = base64.b64encode(LOGO.read_bytes()).decode()

print(
    DOCINFO_TEMPLATE
    .read_text()
    .replace("LOGO_B64_SRC", b64_logo)
)
