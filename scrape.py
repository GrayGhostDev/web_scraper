from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.chrome.options import Options
import time

def scrape_website(website):
    print("Launching Chrome Browser...")

    options = Options()
    options.add_argument("--headless")  # Run in headless mode (optional)

    # Use webdriver_manager to automatically download and manage ChromeDriver
    driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)

    try:
        driver.get(website)
        print("Page loaded...")
        time.sleep(10)  # Wait for 10 seconds (you might want to use explicit waits instead)
        html = driver.page_source

        return html
    finally:
        driver.quit()

# Example usage
if __name__ == "__main__":
    website_url = "https://example.com"  # Replace with the website you want to scrape
    html_content = scrape_website(website_url)
    print(f"Scraped HTML length: {len(html_content)}")